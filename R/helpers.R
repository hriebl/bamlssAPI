pred_obj <- function(model, predictor) {
  return(model$x[[predictor]])
}

set_pred_obj <- function(model, predictor, object) {
  model$x[[predictor]] <- object
  return(model)
}

int_smooths <- function(x) {
  x[x == "p"] <- "model.matrix"
  return(x)
}

ext_smooths <- function(x) {
  x[x == "model.matrix"] <- "p"
  return(x)
}

smt_obj <- function(model, predictor, smooth) {
  pred <- pred_obj(model, predictor)
  smt <- pred$smooth.construct[[int_smooths(smooth)]]
  return(smt)
}

set_smt_obj <- function(model, predictor, smooth, object) {
  pred <- pred_obj(model, predictor)
  pred$smooth.construct[[int_smooths(smooth)]] <- object
  model <- set_pred_obj(model, predictor, pred)
  return(model)
}

par_obj <- function(model, predictor, smooth) {
  smt <- smt_obj(model, predictor, smooth)
  par <- smt$state$parameters
  return(par)
}

set_par_obj <- function(model, predictor, smooth, object) {
  smt <- smt_obj(model, predictor, smooth)
  smt$state$parameters <- object
  model <- set_smt_obj(model, predictor, smooth, smt)
  return(model)
}

#' @export

outdated <- function(x) {
  return(is.null(x) || attr(x, "outdated"))
}

flag_outdated <- function(x) {
  if (!is.null(x)) {
    attr(x, "outdated") <- TRUE
  }

  return(x)
}

flag_updated <- function(x) {
  if (!is.null(x)) {
    attr(x, "outdated") <- FALSE
  }

  return(x)
}

#' @export

response <- function(model) {
  y <- model$y

  if (is.data.frame(y) && ncol(y) == 1L) {
    y <- y[[1L]]
  }

  return(y)
}

#' @export

logLik.apified.bamlss <- function(object, ...) {
  return(loglik(object))
}

#' @importFrom stats nobs
#' @export

nobs.bamlss <- function(object, ...) {
  return(nrow(object$y))
}
