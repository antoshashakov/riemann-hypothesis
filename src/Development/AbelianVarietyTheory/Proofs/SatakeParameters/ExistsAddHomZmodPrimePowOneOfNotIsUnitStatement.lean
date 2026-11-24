module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAddHomZmodPrimePowOneOfNotIsUnit
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic

@[expose] public section

open GlobalTheory.Cong

theorem _root_.GlobalTheory.T.exists_addHom_zmod_prime_pow_one_of_not_isUnit : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (l m : ℕ), l.Prime → ¬ IsUnit (l : R) → ∃ φ : R →+ ZMod (l ^ m), φ 1 = 1 ∧ ∀ x, φ ((l : R) ^ m * x) = 0 := by
  first | exact @GlobalTheory.exists_addHom_zmod_pow_one_of_not_isUnit | exact GlobalTheory.exists_addHom_zmod_pow_one_of_not_isUnit | (intros; apply GlobalTheory.exists_addHom_zmod_pow_one_of_not_isUnit; all_goals assumption)
