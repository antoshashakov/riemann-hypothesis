module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringExtendingRingHom
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.exists_valuationSubring_extending_ringHom : ∀ (W Ω k : Type) [CommRing W] [Field Ω] [Field k] [IsAlgClosed k] (j : W →+* Ω), Function.Injective j → ∀ g : W →+* k, ∃ (U : ValuationSubring Ω) (hU : ∀ w, j w ∈ U) (h : U →+* k), ∀ w, h ⟨j w, hU w⟩ = g w := by
  first | exact @GlobalTheory.ValExt.exists_valuationSubring_ext | exact GlobalTheory.ValExt.exists_valuationSubring_ext | (intros; apply GlobalTheory.ValExt.exists_valuationSubring_ext <;> assumption)
