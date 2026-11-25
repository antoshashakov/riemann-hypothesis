module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceNotPowAdicCompletion
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.exists_place_not_pow_adicCompletion : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → u ≠ 0 → (∀ r : F, r ^ p ≠ u) → ∃ v, v ∉ S₀ ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) u := by
  first | exact @GlobalTheory.CNorm.exists_not_mem_not_pow_completion | exact GlobalTheory.CNorm.exists_not_mem_not_pow_completion | (intros; apply GlobalTheory.CNorm.exists_not_mem_not_pow_completion <;> assumption)
