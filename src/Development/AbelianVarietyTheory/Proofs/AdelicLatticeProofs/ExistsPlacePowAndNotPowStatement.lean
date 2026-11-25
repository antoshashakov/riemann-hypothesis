module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlacePowAndNotPow
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.exists_place_pow_and_not_pow' : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ δ u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → δ ≠ 0 → u ≠ 0 → (∀ r : F, r ^ p ≠ δ) → (∀ (k : ℕ) (r : F), u ≠ δ ^ k * r ^ p) → ∃ v, v ∉ S₀ ∧ (∃ r : v.adicCompletion F, r ^ p = algebraMap F (v.adicCompletion F) δ) ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) u := by
  first | exact @GlobalTheory.CNorm.exists_place_pow_and_not_pow | exact GlobalTheory.CNorm.exists_place_pow_and_not_pow | (intros; apply GlobalTheory.CNorm.exists_place_pow_and_not_pow <;> assumption)
