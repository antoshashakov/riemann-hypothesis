module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruencePrimePowTorsionFree
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic

@[expose] public section

open GlobalTheory.Cong

theorem _root_.GlobalTheory.T.principalCongruence_prime_pow_torsionFree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (l m a : ℕ), l.Prime → ¬ IsUnit (l : R) → 2 ≤ m → ∀ (x : Matrix (Fin a) (Fin a) R) (n : ℕ), 0 < n → (1 + ((l : R) ^ m) • x) ^ n = 1 → x = 0 := by
  first | exact @GlobalTheory.principalCongruence_torsionFree | exact GlobalTheory.principalCongruence_torsionFree | (intros; apply GlobalTheory.principalCongruence_torsionFree; all_goals assumption)
