/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanGO.Examples.LIPO
import VersoManual
import LeanGOManual.Papers

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true

set_option verso.exampleProject "."

set_option verso.exampleModule "LeanGO.Examples.Decision"

#doc (Manual) "Decision-based methods" =>
%%%
htmlSplit := .never
%%%

We provide an interface for _decision-based optimization algorithms_. Such algorithm are described by a sequence of decision rules to decide wether to accept or reject a candidate solution at each iteration, based on the observed data. Decision rules are functions with the signature $`D_n : \Omega^{n + 1} \times \beta^{n + 1} \to [0, 1]`, where $`\Omega` is the search space and $`\beta` is the space of function values (most likely $`\mathbb{R}`). More formally, given a function to optimize $`V : \Omega \to \beta` at each iteration $`n > 0`, the algorithm samples a candidate $`x` from a distribution $`\mu` on $`\Omega` and accepts it with probability $`D_n(C_n, V(C_n), x)`.

We define {name Decision}`Decision` as a special case of the `Algorithm` structure, for which the Markov kernel at iteration $`n` is defined through the decision rules $`(D_n)_{n \in \mathbb{N}}`. Measurability assumptions are required on the decision rules for the kernels to be well-defined and we only support $`\{0, 1\}`-valued decision rules at the moment.

{docstring Decision}
