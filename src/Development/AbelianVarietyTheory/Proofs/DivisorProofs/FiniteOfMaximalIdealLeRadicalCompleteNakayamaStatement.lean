module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfMaximalIdealLeRadicalCompleteNakayama
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.finite_of_maximalIdeal_le_radical_complete_nakayama : ∀ (B R : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → IsLocalHom ψ → maximalIdeal R ≤ ((maximalIdeal B).map ψ).radical → ((residue R).comp ψ).Finite → ψ.Finite := by
  first | exact @GlobalTheory.CompleteNakayamaLocal.finite_of_maximalIdeal_le_radical | exact GlobalTheory.CompleteNakayamaLocal.finite_of_maximalIdeal_le_radical | (intros; apply GlobalTheory.CompleteNakayamaLocal.finite_of_maximalIdeal_le_radical <;> assumption)
