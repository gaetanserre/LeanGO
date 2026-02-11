/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual
open Verso.Genre.Manual

def Malherbe2017 : InProceedings where
  title := inlines!"Global optimization of Lipschitz functions"
  authors := #[inlines!"Cédric Malherbe", inlines!"Nicolas Vayatis"]
  year := 2017
  booktitle := inlines!"International conference on machine learning"

def Hansen1996 : InProceedings where
  title := inlines!"Adapting arbitrary normal mutation distributions in evolution strategies: The covariance matrix adaptation"
  authors := #[inlines!"Nikolaus Hansen", inlines!"Andreas Ostermeier"]
  year := 1996
  booktitle := inlines!"Proceedings of IEEE international conference on evolutionary computation"

def Tulcea1949 : InProceedings where
  title := inlines!"Mesures dans les espaces produits"
  authors := #[inlines!"CT Ionescu Tulcea"]
  year := 1949
  booktitle := inlines!"Atti Accad. Naz. Lincei Rend"
