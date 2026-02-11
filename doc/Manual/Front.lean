/-
 - Created in 2025 by Gaëtan Serré
-/

import Manual.Algorithm
import Manual.Examples.Examples
import Manual.Papers
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "Formalization of stochastic iterative optimization algorithm" =>
%%%
authors := ["Gaëtan Serré"]
shortTitle := "Formalization of optimization algorithms"
%%%

This documentation is associated with the paper [_A Unifying Framework for Global Optimization: From Theory to Formalization_](https://arxiv.org/abs/2508.20671) by Gaëtan Serré, Argyris Kalogeratos and Nicolas Vayatis. It presents an abstract definition of stochastic iterative optimization algorithms along with a construction of probability measures on the space of the iterations of the algorithm. This documentation describes the `L∃∀N` formalization of this framework. To illustrate the framework, we also present the formalization of two algorithms: _Pure Random Search_ and _LIPO_ {citep Malherbe2017}[]. To see a more complete example of the use of the framework, see the [formalization of *Proposition 1*](https://gaetanserre.fr/LipoCons/) of Malherbe and Vayatis (2017)*¹*.

{include 0 Manual.Algorithm}

{include 0 Manual.Examples.Examples}
