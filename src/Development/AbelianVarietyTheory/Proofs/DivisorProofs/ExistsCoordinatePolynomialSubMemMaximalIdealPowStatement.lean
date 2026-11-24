module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatePolynomialSubMemMaximalIdealPow
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply

@[expose] public section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

theorem _root_.GlobalTheory.T.exists_coordinate_polynomial_sub_mem_maximalIdeal_pow : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (z : Fin n → A), maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → ∀ (k : ℕ) (f : A), ∃ p ∈ Subring.closure (Set.range inc ∪ Set.range z), f - p ∈ maximalIdeal A ^ k := by
  first | exact @GlobalTheory.exists_mem_closure_sub_mem_maximalIdeal_pow | exact GlobalTheory.exists_mem_closure_sub_mem_maximalIdeal_pow | (intros; apply GlobalTheory.exists_mem_closure_sub_mem_maximalIdeal_pow <;> assumption)
