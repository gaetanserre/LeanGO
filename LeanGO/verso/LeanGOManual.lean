/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under GNU GPL 3.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import VersoManual

import LeanGOManual.Front

open Verso.Genre.Manual Verso.Output.Html

def extraHead : Array Verso.Output.Html := #[
    {{<link rel="icon" type="image/x-icon" href="static/favicon.svg"/>}},
    {{<link rel="stylesheet" href="static/style.css"/>}},
    {{<script src="static/scripts.js"></script>}},
]

def git := "https://github.com/gaetanserre/LeanGO"

def config : RenderConfig := {
  extraHead := extraHead,
  sourceLink := some git,
  issueLink := some (git ++ "/issues"),
}

def main := manualMain (%doc LeanGOManual.Front) (config := config)
