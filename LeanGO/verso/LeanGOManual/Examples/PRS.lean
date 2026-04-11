/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanGO.Examples.PRS
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true

set_option verso.exampleProject "."

set_option verso.exampleModule "LeanGO.Examples.PRS"

#doc (Manual) "Pure Random Search" =>
%%%
htmlSplit := .never
%%%

The Pure Random Search (PRS) algorithm is a simple stochastic iterative global optimization algorithm that samples uniformly from the input space at each iteration using a fixed
probability measure {anchorTerm PRS}`μ`. It can be represented in our framework as follows:

{docstring PRS}

```anchor PRS
noncomputable def PRS : Algorithm α β where
  ν := μ
  kernel_iter _ := Kernel.const _ μ
```
