/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import VersoManual
import Manual.Examples.PRS
import Manual.Examples.LIPO
import Manual.Examples.RankOpt

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "Some examples" =>
%%%
htmlSplit := .never
%%%

In this page, we present two examples of algorithms encompassed by our framework: the Pure Random Search (PRS) and the LIPO algorithms. The formalization of these algorithms in our framework relies on the definition of the initial probability measure and the Markov kernels that define how to sample the next element based on the previous ones.

{include 0 Manual.Examples.PRS}

{include 0 Manual.Examples.LIPO}

{include 0 Manual.Examples.RankOpt}
