/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import VersoManual
import LeanGOManual.Examples.PRS
import LeanGOManual.Examples.LIPO
import LeanGOManual.Examples.RankOpt

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true
set_option linter.dupNamespace false

#doc (Manual) "Some examples" =>
%%%
htmlSplit := .never
%%%

In this page, we present two examples of algorithms encompassed by our framework: the Pure Random Search (PRS) and the LIPO algorithms. The formalization of these algorithms in our framework relies on the definition of the initial probability measure and the Markov kernels that define how to sample the next element based on the previous ones.

{include 0 LeanGOManual.Examples.PRS}

{include 0 LeanGOManual.Examples.LIPO}

{include 0 LeanGOManual.Examples.RankOpt}
