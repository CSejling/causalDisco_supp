library(pcalg)
library(splines)
library(nnet)
library(gtools)
library(rje)
library(dplyr)

## causalDisco adjustments: 
# Allowing for categorical responses, weights in the conditional independence tests, a conservative collider orientation option, and then finally algorithm 2 from Perkovic et. al (2018).

makeSuffStat <- function(data, sample_weights = NULL, type, ...) {
  #browser()
  if (type == "regTest") {
    bin <- unlist(sapply(data, function(x) length(unique(x)) == 2))
    cat <- unlist(sapply(data, function(x) length(unique(x)) > 2 & is.factor(x)))
    suff <- list(data = data, binary = bin, categorical = cat)
    #  if (!is.null(order)) suff$order <- order
  } else if (type == "corTest") {
    suff <- list(C = stats::cor(data), n = nrow(data))
  } else {
    stop(paste(type, "is not a supported type for",
               "autogenerating a sufficient statistic"))
  }
  
  #else suff <- list(data = data)
  #suff$otherArgs <- list(...)
  
  suff$sample_weights <- sample_weights
  
  return(suff)
}

regTestEachDir <- function(x, y, S, suffStat) {
  
  #args <- suffStat$otherArgs
  #if (!is.null(args) && "df" %in% names(args)) {
  #  dfs <- args$df
  #} else
  
  #dfs
  dfs <- 3
  dfString <- paste(", df = ", dfs, ")", sep  = "")
  
  #Unpack suffStat
  data <- suffStat$data
  binary <- suffStat$binary
  categorical <- suffStat$categorical
  sample_weights <- suffStat$sample_weights
  vnames <- names(data)
  #order <- suffStat$order

  
  #Store info: is x binary?
  binx <- binary[x]
  catx <- categorical[x]
  
  #Store info: which S are binary?
  binS <- intersect(S, which(binary))
  catS <- intersect(S, which(categorical))
  numS <- setdiff(S, c(binS,catS))
  
  #extract variable names
  x <- vnames[x]
  y <- vnames[y]
  S_bin <- vnames[binS]
  S_cat <- vnames[catS]
  S_num <- vnames[numS]
  allS <- c(S_bin, S_cat, S_num)
  
  # A little fix for different missings in each variable (to get anova to work):
  
  data[is.na(data[,y]),x] <- NA
  data[is.na(data[,x]),y] <- NA
  
  #add spline to num x, factor to binary and categorical x
  if (!binx & !catx) {
    if (dfs > 0) x <- paste("ns(", x, dfString, sep = "")
    #    x <- paste("ns(", x, dfString, sep = "")
  } else x <- paste("factor(", x, ")", sep = "")
  
  
  #add spline to num S, factor to binary s
  #S_num <- NULL
  if (length(S_num > 0)) {
    S_num <- paste("ns(", S_num, dfString, sep = "")
    # browser()
  }
  if (length(S_bin > 0)) S_bin <- paste("factor(", S_bin, ")", sep = "")
  if (length(S_cat > 0)) S_cat <- paste("factor(", S_cat, ")", sep = "")
  S <- c(S_bin, S_num, S_cat, "1")
  
  #wrap factor around binary f
    if (binary[y]) {
      fam <- "binomial"
    } else if(categorical[y]){
      fam <- "multinomial"
    } else fam <- "gaussian"

  
  if (fam %in% c("binomial")) {
    y <- paste("factor(", y, ")", sep = "")
  }
  
  #make formulas
  f1 <- as.formula(paste(y, "~", paste(S, collapse = " + ")))
  f2 <- update(f1, as.formula(paste(". ~ . + ", x, sep = "")))
  
  #troubleshooting
  # wp <- FALSE
  
  #fit models
  if (!(fam=="multinomial")){
  m1 <- suppressWarnings(glm(f1, data = data, family = fam, weights = sample_weights))
  m2 <- suppressWarnings(glm(f2, data = data, family = fam, weights = sample_weights))
  }
  if (fam=="multinomial"){
  m1 <- suppressWarnings(multinom(f1, data = data, weights = sample_weights, trace = FALSE))
  m2 <- suppressWarnings(multinom(f2, data = data, weights = sample_weights, trace = FALSE))
  }
  
  #troubleshooting
  # if (m1$boundary | m2$boundary) browser()
  
  #test
  if (!(fam=="multinomial")){
  
  #if convergence fails, output 0 (corresponds to no sep)
  if (!m1$converged | !m2$converged) return(0)  
  
  p <- anova(m1, m2, test = "LRT")$`Pr(>Chi)`[2]
  }
    
  if (fam=="multinomial"){
  if (m1$convergence>0 | m2$convergence>0) return(0)  # For multinom it is the convergence status from optim (0 ~ completion, non-zero ~ not completion)
    
  p <- anova(m1, m2, test = "Chisq")$`Pr(Chi)`[2]
  } 
  
  return(p)
  
  #not allowed on CRAN, but saves method look-up time
  #stats:::anova.glm(m1, m2, test = "LRT")$`Pr(>Chi)`[2]
}

regTest <- function(x, y, S, suffStat) {
  p1 <- regTestEachDir(x, y, S, suffStat)
  p2 <- regTestEachDir(y, x, S, suffStat)
  
  max(p1,p2)
}

dirTest <- function(test, vnames, order) {
  thistest <- function(x, y, S, suffStat) {
    
    #check if we need to conduct the test at all
    #(whether S occurs strictly after both
    # x and y in order)
    snames <- vnames[S] #NOTE: CHECK IF THIS IS CORRECT FOR EMPTY S
    xname <- vnames[x]
    yname <- vnames[y]
    laterS <- FALSE
    i <- 1
    nS <- length(snames)
    while(!laterS & i <= nS) {
      s <- snames[i]
      afterx <- is.after(s, xname, order)
      aftery <- is.after(s, yname, order)
      if (afterx & aftery) laterS <- TRUE
      i <- i + 1
    }
    if (laterS) {
      return(0)
    }
    
    #If no order problem, use test function:
    do.call(test, list(x = x, y = y, S = S, suffStat = suffStat))
  }
  thistest
}

tpc <- function(data, order, sparsity = 10^(-1), test = regTest, testStr = "regTest", conservative = FALSE,
                suffStat = NULL, sample_weights = NULL, output = "tpdag", m.max = Inf,...) { 
  
  #check arguments
  if (!output %in% c("tpdag", "tskeleton")) {
    stop("Output must be tpdag or tskeleton.")
  }
  
  #variable names
  vnames <- names(data)
  
  #make testing procedure that does not condition on
  #the future
  thisDirTest <- dirTest(test, vnames, order) 
  
  #Construct sufficient statistic for built-in tests
  if (is.null(suffStat)) {
    #thisTestName <- deparse(match.call()[["test"]])
    thisTestName <- testStr #deparse(substitute(test))
    if (thisTestName == "regTest") {
      thisSuffStat <- makeSuffStat(data, sample_weights = sample_weights, type = "regTest")
      sample_weights <- thisSuffStat$sample_weights
    } else if (thisTestName == "corTest") {
      thisSuffStat <- makeSuffStat(data, sample_weights = sample_weights, type = "corTest")
      sample_weights <- thisSuffStat$sample_weights
    } else {
      stop(paste("suffStat needs to be supplied",
                 "when using a non-builtin test."))
    }
  } else {
    thisSuffStat <- suffStat
    if (!is.null(sample_weights)){
      thisSuffStat$sample_weights <- sample_weights
    }
  }
  
  
  #Learn skeleton
  skel <- pcalg::skeleton(suffStat = thisSuffStat,
                   indepTest = thisDirTest,
                   alpha = sparsity,
                   labels = vnames,
                   m.max = m.max,
                   method = "stable.fast")
  ntests <- sum(skel@n.edgetests)
  
  
  if (output == "tskeleton") {
    out <- list(amat = skel@amat, order = order, psi = sparsity,
                ntest = ntests)
    class(out) <- "tskeleton"
  } else { #case: output == "tpdag"
    
    #Direct edges
    res <- tpdag(skel, order = order, conservative = conservative, data = data, weights = sample_weights, sparsity = sparsity)
    
    #Pack up output
    out <- list(amat = amat(res), order = order, psi = sparsity,
                ntests = ntests)
    class(out) <- "tpdag"
  }
  
  out
}

## Adding a faithfulness check before putting v structures

vOrientTemporal <- function(skelAmat, sepsets, conservative = FALSE, data = NULL, weights = NULL, sparsity = NULL) { # Algorithm step 3.1 - Fixed for 
  vnames <- rownames(skelAmat)
  nvar <- nrow(skelAmat)
  
  if (conservative == TRUE){ # Then we need some extra tests, hence we need to model like in the main function using splines and factors
    
    vnamesModel <- vnames
    
    # for add spline to num x, factor to binary and categorical x
    dfs <- 3
    dfString <- paste(", df = ", dfs, ")", sep  = "")
    
    for (j in 1:length(vnames)){
    
    if (is.factor(data[,vnames[j]])){
      vnamesModel[j] <- paste("factor(", vnamesModel[j], ")", sep = "")
    }
    
    if (is.numeric(data[,vnames[j]])){
      vnamesModel[j] <- paste("ns(", vnamesModel[j], dfString, sep = "")
    }
    }
  }
  
  for (i in 1:nvar) {
    theseAdj <- findAdjacencies(skelAmat, i)
    
    #if there are at least two adjacent nodes
    if (length(theseAdj) >= 2) {
      
      adjpairs <- gtools::combinations(length(theseAdj), 2, v = theseAdj) #gtools
      
      npairs <- nrow(adjpairs)
      
      if (npairs >= 1) {
        
        for (j in 1:npairs) {
          thisPair <- adjpairs[j,]
          j1 <- thisPair[1]
          j2 <- thisPair[2]
          thisPairAdj <- j2 %in% findAdjacencies(skelAmat, j1) # Are the two neighbours adjacent to each other?
          
          #if pair is not adjacent (unmarried)
          if (!thisPairAdj) {
            
            sepset1 <- sepsets[[j1]][[j2]]
            sepset2 <- sepsets[[j2]][[j1]]
            
            unionSep <- c(sepset1, sepset2) # By article 2013, a separting node is saved in both sets.
            
            status <- 'faithful'
            
            if (conservative == TRUE){
              
              # default status
              status <- 'unfaithful'
              
              nbrsA <- findAdjacencies(skelAmat,j1)
              nbrsB <- findAdjacencies(skelAmat,j2)
              
              pSepSetsA <- powerSet(nbrsA,m=length(nbrsA))
              pSepSetsB <- powerSet(nbrsB,m=length(nbrsB))

              
              # Doing the tests
              
              if (is.factor(data[,vnames[j1]]) & n_distinct(data[,vnames[j1]])>2){
                fam <- "multinomial"
              }
              
              if (is.factor(data[,vnames[j1]]) & n_distinct(data[,vnames[j1]])==2){
                fam <- "binomial"
              }
              
              if (is.numeric(data[,vnames[j1]])){
                fam <- "gaussian"
              }
              
              pSetsA <- numeric(0)
              
              for (k in 1:length(pSepSetsA)){
              
              symb <- "+"
              if (paste(vnames[pSepSetsA[[k]]], collapse="+") == ""){
                symb <- ""
              }
                
              f1 <- as.formula(paste(str_c(vnames[j1], "~", vnamesModel[j2], " + ", paste(vnamesModel[pSepSetsA[[k]]], collapse="+"), symb, "1")))
              f2 <- as.formula(paste(str_c(vnames[j1], "~", "1", symb, paste(vnamesModel[pSepSetsA[[k]]], collapse="+"))))
              
              # Taking only non-missing stuff

              workdata <- data[!is.na(data[,vnames[j2]]),]
              workweights <- weights[!is.na(data[,vnames[j2]])]
              
              #fit models
              if (!(fam=="multinomial")){
                m1 <- suppressWarnings(glm(f1, data = workdata, family = fam, weights = workweights))
                m2 <- suppressWarnings(glm(f2, data = workdata, family = fam, weights = workweights))
              }
              if (fam=="multinomial"){
                m1 <- suppressWarnings(multinom(f1, data = workdata, weights = workweights, trace = FALSE))
                m2 <- suppressWarnings(multinom(f2, data = workdata, weights = workweights, trace = FALSE))
              }
              
              #troubleshooting
              # if (m1$boundary | m2$boundary) browser()
              
              #test 
              if (!(fam=="multinomial")){
                
                #if convergence fails, output 0 (corresponds to no sep, i.e. p<sparsity)
                if (!m1$converged | !m2$converged){
                  p <- 0
                }   
                else{
                  p <- anova(m1, m2, test = "LRT")$`Pr(>Chi)`[2]
                }
              }
              
              if (fam=="multinomial"){
                if (m1$convergence>0 | m2$convergence>0){
                  p <- 0
                }     
                else{
                  p <- anova(m1, m2, test = "Chisq")$`Pr(Chi)`[2]
                }
              } 
              
              pSetsA[k] <- p
              
              }
              
              if (is.factor(data[,vnames[j2]]) & n_distinct(data[,vnames[j2]])>2){
                fam <- "multinomial"
              }
              
              if (is.factor(data[,vnames[j2]]) & n_distinct(data[,vnames[j2]])==2){
                fam <- "binomial"
              }
              
              if (is.numeric(data[,vnames[j2]])){
                fam <- "gaussian"
              }
              
              pSetsB <- numeric(0)
              
              for (k in 1:length(pSepSetsB)){
                
                symb <- "+"
                if (paste(vnames[pSepSetsB[[k]]], collapse="+") == ""){
                  symb <- ""
                }
                
                f1 <- as.formula(paste(str_c(vnames[j2], "~", vnamesModel[j1], " + ", paste(vnamesModel[pSepSetsB[[k]]], collapse="+"), symb, "1")))
                f2 <- as.formula(paste(str_c(vnames[j2], "~", "1", symb, paste(vnamesModel[pSepSetsB[[k]]], collapse="+"))))
                
                # Taking only non-missing stuff
                
                workdata <- data[!is.na(data[,vnames[j1]]),]
                workweights <- weights[!is.na(data[,vnames[j1]])]
                
                #fit models
                if (!(fam=="multinomial")){
                  m1 <- suppressWarnings(glm(f1, data = workdata, family = fam, weights = workweights))
                  m2 <- suppressWarnings(glm(f2, data = workdata, family = fam, weights = workweights))
                }
                if (fam=="multinomial"){
                  m1 <- suppressWarnings(multinom(f1, data = workdata, weights = workweights, trace = FALSE))
                  m2 <- suppressWarnings(multinom(f2, data = workdata, weights = workweights, trace = FALSE))
                }
                
                
                #test
                if (!(fam=="multinomial")){
                  
                  #if convergence fails, output 0 (corresponds to no sep)
                  if (!m1$converged | !m2$converged){
                    p <- 0
                  }   
                  else{
                    p <- anova(m1, m2, test = "LRT")$`Pr(>Chi)`[2]
                  }
                }
                
                if (fam=="multinomial"){
                  if (m1$convergence>0 | m2$convergence>0){
                    p <- 0
                  }     
                  else{
                    p <- anova(m1, m2, test = "Chisq")$`Pr(Chi)`[2]
                  }
                } 
                
                pSetsB[k] <- p
                
              }
              
              sSepSetsA <- pSepSetsA[pSetsA>sparsity]
              sSepSetsB <- pSepSetsB[pSetsB>sparsity]
              
              # The conditions from pcalg software article for checking faithfulness:
              
              if (((!(i %in% unionSep))) & (sum(unlist(lapply(c(sSepSetsA, sSepSetsB), function(x) i %in% x)))==0)){ 
                status <- 'faithful'
              }
              
              if ((((i %in% unionSep))) & (sum(unlist(lapply(c(sSepSetsA, sSepSetsB), function(x) i %in% x)))==length(c(sSepSetsA, sSepSetsB)))){
                status <- 'faithful'
              }
              
              if (length(c(sSepSetsA,sSepSetsB))==0){ # They were supposed to not be adjacent as per one of the outer loop conditions!
                status <- 'unfaithful'
              }
              
            }
            
            #if middle node is not a separator of two other nodes and potential v-structure is deemed faithful
            if (!(i %in% sepset1) & !(i %in% sepset2) & status == 'faithful') {
              
              #if this does not contradict directional information
              #already in the graph
              if (skelAmat[i,j1] == 1 & skelAmat[i,j2] == 1) { # If we have not already ruled out that j1 -> i may be true and j2 -> may be true, then that is the case.
                skelAmat[j1, i] <- 0
                skelAmat[j2, i] <- 0
              }
            }
          }
        }
      }
    }
  }
  return(skelAmat)
}


tpdag <- function(skel, order, conservative = FALSE, data = NULL, weights = NULL, sparsity = NULL) {
  thisAmat <- amat(skel)
  
  tempSkelAmat <- orderRestrictAmat(thisAmat, order = order) # Algorithm step 3.0
  
  vOriented <- vOrientTemporal(skelAmat = tempSkelAmat, sepsets = skel@sepset, conservative = conservative, data = data, weights = weights, sparsity = sparsity) # Algorithm step 3.1
  
  # vOriented apparently returns a 0 in the base case for followup sample?
  
  pcalg::addBgKnowledge(vOriented, checkInput = FALSE) # Algorithm step 3.2
}


# For effect estimation

algorithm2 <- function(PDAG, x, y){ # A function for finding joint parent sets in one outcome node and one intervention node, due to Perkovic et. al. (2018).
  
  Sib1 <- which(PDAG$amat[x,] == 1 & PDAG$amat[,x] == 1)
  SibSub <- powerSet(Sib1)[-1]
  
  localBg <- numeric(0)
  PossPa <- list()
  
  k <- 1
  l <- 1
  for (s in SibSub){
  for (i in s){
    localBg <- rbind(localBg,c(i,x))
  }
  for (j in SibSub[-l]){
    localBg <- rbind(localBg,c(x,j))
  }
  l <- l + 1
  if (!is.null(addBgKnowledge(PDAG$amat, x=localBg[,1], y = localBg[,2], checkInput = TRUE))){
    amat <- addBgKnowledge(PDAG$amat, x=localBg[,1], y = localBg[,2], checkInput = TRUE)
    PossPa[k] <- c(which(amat[x,]==1),s)
    k <- k + 1
  }
  }
  
  return(PossPa)
}

