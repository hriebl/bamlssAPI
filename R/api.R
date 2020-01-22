#' Enable API for a bamlss model
#'
#' This function enables the API for the given bamlss model. Afterwards, you
#' can use the functions from the bamlssAPI package with the model.
#'
#' @param model A [`bamlss::bamlss`] or [`bamlss::bamlss.frame`] object.
#' @param propose A string containing the name of a bamlss propose function for
#'   model terms. Defaults to `"iwlsC_gp"`. See [bamlss::GMCMC()].
#'
#' @return The API-enabled model.
#'
#' @examples
#' library(bamlss)
#' y <- rnorm(10)
#' b <- bamlss(y ~ 1)
#' b <- apify(b)
#'
#' @export

apify <- function(model, propose = "iwlsC_gp") {
  model$x <- bamlss::bamlss.engine.setup(model$x, propose = propose)

  if ("parameters" %in% names(model)) {
    par <- bamlss::parameters(model)
    names(par) <- sub("^(.*?\\.)s\\.", "\\1", names(par))
    ss <- strsplit(names(par), ".", fixed = TRUE)

    for (i in seq_along(par)) {
      model <- set_parameters(model, predictor = ss[[i]][1],
                              smooth = ss[[i]][2], values = par[i],
                              names = ss[[i]][3])
    }
  }

  for (predictor in predictors(model)) {
    pred <- pred_obj(model, predictor)

    ml <- bamlss:::make.link2(model$family$links[predictor])
    pred$linkinv <- ml$linkinv

    model <- set_pred_obj(model, predictor, pred)

    for (smooth in smooths(model, predictor)) {
      smt <- smt_obj(model, predictor, smooth)

      # the following changes to the smooth object are the same as in the
      # bamlss::GMCMC() function

      smt$state$fitted.values <- NULL

      if (!inherits(smt, "special")) {
        smt$XW <- t(smt$X)
        smt$XWX <- crossprod(smt$X)
      }

      smt$dmvnorm_log <- bamlss:::dmvnorm_log

      if (!isTRUE(smt$fxsp)) {
        smt$fxsp <- FALSE
      }

      if (!is.function(smt$propose) && is.function(smt$xt$propose)) {
        smt$propose <- smt$xt$propose
      }

      smt$penaltyFunction <- as.integer(vapply(smt$S, is.function, FALSE))

      model <- set_smt_obj(model, predictor, smooth, smt)
    }
  }

  model$parameters <- NULL
  model$fitted.values <- NULL

  model <- update_logpost(model)

  class(model) <- c("apified.bamlss", class(model))

  return(model)
}


#' Extract predictor and smooth names
#'
#' The `predictors` function extracts the names of the predictors from the
#' given bamlss model, while the `smooths` function returns the names of the
#' smooths in one predictor.
#'
#' @usage
#' predictors(model)
#' smooths(model, predictor)
#'
#' @param model An [API-enabled][apify] bamlss model.
#' @param predictor A string containing the name of one predictor in the model.
#'
#' @return A character vector containing either the names of the predictors or
#'   the names of the smooths.
#'
#' @examples
#' library(bamlss)
#' y <- rnorm(10)
#' b <- bamlss(y ~ 1)
#' b <- apify(b)
#' predictors(b)
#' smooths(b, predictor = predictors(b)[1])
#'
#' @aliases smooths
#' @export

predictors <- function(model) {
  return(model$family$names)
}

#' @export

smooths <- function(model, predictor) {
  pred <- pred_obj(model, predictor)
  smooths <- ext_smooths(names(pred$smooth.construct))
  return(smooths)
}


# parameters & set_parameters -------------------------------------------------

#' @export

parameters <- function(model, predictor, smooth, names = NULL, type = NULL) {
  par <- par_obj(model, predictor, smooth)

  if (smooth == "p" && !is.null(type) && type == "b") {
    type <- NULL
  }

  if (!is.null(names)) {
    par <- par[names[names %in% base::names(par)]]
  } else if (!is.null(type)) {
    par <- par[grep(paste0("^", type), base::names(par))]
  } else {
    attr(par, "fitted.values") <- NULL
  }

  return(par)
}

#' @export

set_parameters <- function(model, predictor, smooth, values, names = NULL,
                           type = NULL) {
  par <- par_obj(model, predictor, smooth)

  if (!is.null(names)) {
    par[names[names %in% base::names(par)]] <- values
  } else if (!is.null(type)) {
    par[grep(paste0("^", type), base::names(par))] <- values
  } else {
    par[] <- values
  }

  model <- set_par_obj(model, predictor, smooth, par)

  fx <- flag_outdated(fx(model, predictor, smooth))
  model <- set_fx(model, predictor, smooth, fx)

  eta <- flag_outdated(eta(model, predictor))
  model <- set_eta(model, predictor, eta)

  theta <- flag_outdated(theta(model, predictor))
  model <- set_theta(model, predictor, theta)

  loglik <- flag_outdated(loglik(model))
  model <- set_loglik(model, loglik)

  logprior <- flag_outdated(smooth_logprior(model, predictor, smooth))
  model <- set_smooth_logprior(model, predictor, smooth, logprior)

  logprior <- flag_outdated(model_logprior(model))
  model <- set_model_logprior(model, logprior)

  logpost <- flag_outdated(logpost(model))
  model <- set_logpost(model, logpost)

  return(model)
}


# fx, set_fx & update_fx ------------------------------------------------------

#' @export

fx <- function(model, predictor, smooth) {
  par <- par_obj(model, predictor, smooth)
  fx <- attr(par, "fitted.values")
  return(fx)
}

set_fx <- function(model, predictor, smooth, values) {
  par <- par_obj(model, predictor, smooth)
  attr(par, "fitted.values") <- values
  model <- set_par_obj(model, predictor, smooth, par)
  return(model)
}

#' @export

update_fx <- function(model, predictor, smooth) {
  fx <- fx(model, predictor, smooth)

  if (outdated(fx)) {
    smt <- smt_obj(model, predictor, smooth)
    fx <- smt$fit.fun(smt$X, parameters(model, predictor, smooth))
    model <- set_fx(model, predictor, smooth, flag_updated(fx))
  }

  return(model)
}


# eta, set_eta & update_eta ---------------------------------------------------

#' @export

eta <- function(model, predictor) {
  pred <- pred_obj(model, predictor)
  eta <- pred$state$eta
  return(eta)
}

set_eta <- function(model, predictor, values) {
  pred <- pred_obj(model, predictor)
  pred$state$eta <- values
  model <- set_pred_obj(model, predictor, pred)
  return(model)
}

#' @export

update_eta <- function(model, predictor) {
  eta <- eta(model, predictor)

  if (outdated(eta)) {
    eta <- 0

    for (smooth in smooths(model, predictor)) {
      model <- update_fx(model, predictor, smooth)
      eta <- eta + fx(model, predictor, smooth)
    }

    model <- set_eta(model, predictor, flag_updated(eta))
  }

  return(model)
}


# theta, set_theta & update_theta ---------------------------------------------

#' @export

theta <- function(model, predictor) {
  pred <- pred_obj(model, predictor)
  theta <- pred$state$theta
  return(theta)
}

set_theta <- function(model, predictor, values) {
  pred <- pred_obj(model, predictor)
  pred$state$theta <- values
  model <- set_pred_obj(model, predictor, pred)
  return(model)
}

#' @export

update_theta <- function(model, predictor) {
  theta <- theta(model, predictor)

  if (outdated(theta)) {
    pred <- pred_obj(model, predictor)
    model <- update_eta(model, predictor)
    theta <- pred$linkinv(eta(model, predictor))
    model <- set_theta(model, predictor, flag_updated(theta))
  }

  return(model)
}


# loglik, set_loglik & update_loglik ------------------------------------------

#' @export

loglik <- function(model) {
  return(model$x$state$loglik)
}

set_loglik <- function(model, value) {
  model$x$state$loglik <- value
  return(model)
}

#' @export

update_loglik <- function(model) {
  loglik <- loglik(model)

  if (outdated(loglik)) {
    theta <- vector("list", length(predictors(model)))
    names(theta) <- predictors(model)

    for (predictor in predictors(model)) {
      model <- update_theta(model, predictor)
      theta[[predictor]] <- theta(model, predictor)
    }

    loglik <- model$family$loglik(response(model), theta)
    model <- set_loglik(model, flag_updated(loglik))
  }

  return(model)
}


# smooth_logprior, set_smooth_logprior & update_smooth_logprior ---------------

#' @export

smooth_logprior <- function(model, predictor, smooth) {
  smt <- smt_obj(model, predictor, smooth)
  logprior <- smt$state$logprior
  return(logprior)
}

set_smooth_logprior <- function(model, predictor, smooth, value) {
  smt <- smt_obj(model, predictor, smooth)
  smt$state$logprior <- value
  model <- set_smt_obj(model, predictor, smooth, smt)
  return(model)
}

#' @export

update_smooth_logprior <- function(model, predictor, smooth) {
  logprior <- smooth_logprior(model, predictor, smooth)

  if (outdated(logprior)) {
    smt <- smt_obj(model, predictor, smooth)
    logprior <- flag_updated(smt$prior(parameters(model, predictor, smooth)))
    model <- set_smooth_logprior(model, predictor, smooth, logprior)
  }

  return(model)
}


# model_logprior, set_model_logprior & update_model_logprior ------------------

#' @export

model_logprior <- function(model) {
  return(model$x$state$logprior)
}

set_model_logprior <- function(model, value) {
  model$x$state$logprior <- value
  return(model)
}

#' @export

update_model_logprior <- function(model) {
  logprior <- model_logprior(model)

  if (outdated(logprior)) {
    logprior <- 0

    for (predictor in predictors(model)) {
      for (smooth in smooths(model, predictor)) {
        model <- update_smooth_logprior(model, predictor, smooth)
        logprior <- logprior + smooth_logprior(model, predictor, smooth)
      }
    }

    model <- set_model_logprior(model, flag_updated(logprior))
  }

  return(model)
}


# logpost, set_logpost & update_logpost ---------------------------------------

#' @export

logpost <- function(model) {
  return(model$x$state$logpost)
}

set_logpost <- function(model, value) {
  model$x$state$logpost <- value
  return(model)
}

#' @export

update_logpost <- function(model) {
  logpost <- logpost(model)

  if (outdated(logpost)) {
    model <- update_loglik(model)
    loglik <- loglik(model)

    model <- update_model_logprior(model)
    logprior <- model_logprior(model)

    logpost <- loglik + logprior

    model <- set_logpost(model, flag_updated(logpost))
  }

  return(model)
}


# propose & accept ------------------------------------------------------------

#' @export

propose <- function(model, predictor, smooth) {
  smt <- smt_obj(model, predictor, smooth)

  par <- list(list(par_obj(model, predictor, smooth)))

  names(par) <- predictor
  names(par[[predictor]]) <- smooth

  eta <- lapply(predictors(model), function(predictor) {
    eta(update_eta(model, predictor), predictor)
  })

  names(eta) <- predictors(model)

  proposal <- smt$propose(
    family   = model$family,
    theta    = par,
    id       = c(predictor, smooth),
    eta      = eta,
    y        = response(model),
    data     = smt,
    zworking = rep(0, nobs(model)),
    resids   = rep(0, nobs(model)),
    rho      = new.env()
  )

  return(proposal)
}

#' @export

accept <- function(model, predictor, smooth, proposal) {
  model <- set_parameters(model, predictor, smooth, proposal$parameters)

  fx <- attr(proposal$parameters, "fitted.values")
  model <- set_fx(model, predictor, smooth, flag_updated(fx))

  # edf <- unname(proposal$extra["edf"])
  # model <- set_edf(model, predictor, smooth, flag_updated(edf))

  return(model)
}


# grad_loglik, grad_logprior & grad_logpost -----------------------------------

#' @export

grad_loglik <- function(model, predictor, smooth) {
  theta <- lapply(predictors(model), function(predictor) {
    theta(update_theta(model, predictor), predictor)
  })

  names(theta) <- predictors(model)

  score <- model$family$score[[predictor]](response(model), theta)

  smt <- smt_obj(model, predictor, smooth)
  X <- smt$X

  if (!is.null(smt$binning)) {
    X <- X[smt$binning$match.index, , drop = FALSE]
  }

  grad <- drop(crossprod(X, score))
  tau2 <- parameters(model, predictor, smooth, type = "tau2")
  grad <- c(grad, rep(0, length(tau2)))

  return(grad)
}

#' @export

grad_logprior <- function(model, predictor, smooth) {
  smt <- smt_obj(model, predictor, smooth)

  beta <- parameters(model, predictor, smooth, type = "b")
  tau2 <- parameters(model, predictor, smooth, type = "tau2")

  gb <- rep(0, length(beta))
  gt <- rep(0, length(tau2))

  for (i in seq_along(tau2)) {
    S <- smt$S[[i]]

    if (is.function(S)) {
      S <- S(c(beta, tau2, smt$fixed.hyper))
    }

    gb <- gb - S %*% (beta / tau2[i])

    tmp <- -smt$rank[i] / (2 * tau2[i])
    tmp <- tmp + sum(beta * (S %*% beta)) / (2 * tau2[i]^2)
    tmp <- tmp - (smt$a + 1) / tau2[i] + smt$b / tau2[i]^2

    gt[i] <- tmp
  }

  grad <- c(gb, gt)

  return(grad)
}

#' @export

grad_logpost <- function(model, predictor, smooth) {
  grad <- grad_loglik(model, predictor, smooth)
  grad <- grad + grad_logprior(model, predictor, smooth)
  return(grad)
}


# hess_loglik, hess_logprior & hess_logpost -----------------------------------

#' @export

hess_loglik <- function(model, predictor, smooth) {
  theta <- lapply(predictors(model), function(predictor) {
    theta(update_theta(model, predictor), predictor)
  })

  names(theta) <- predictors(model)

  hess <- model$family$hess[[predictor]](response(model), theta)

  smt <- smt_obj(model, predictor, smooth)
  X <- smt$X

  if (!is.null(smt$binning)) {
    X <- X[smt$binning$match.index, , drop = FALSE]
  }

  # this is the same as t(X) %*% diag(hess) %*% X, but much faster
  hess <- crossprod(X * hess, X)

  return(hess)
}

#' @export

hess_logprior <- function(model, predictor, smooth) {
  smt <- smt_obj(model, predictor, smooth)

  beta <- parameters(model, predictor, smooth, type = "b")
  tau2 <- parameters(model, predictor, smooth, type = "tau2")

  hess <- 0

  for (i in seq_along(tau2)) {
    S <- smt$S[[i]]

    if (is.function(S)) {
      S <- S(c(beta, tau2, smt$fixed.hyper))
    }

    hess <- hess + S / tau2[i]
  }

  return(hess)
}

#' @export

hess_logpost <- function(model, predictor, smooth) {
  hess <- hess_loglik(model, predictor, smooth)
  hess <- hess + hess_logprior(model, predictor, smooth)
  return(hess)
}
