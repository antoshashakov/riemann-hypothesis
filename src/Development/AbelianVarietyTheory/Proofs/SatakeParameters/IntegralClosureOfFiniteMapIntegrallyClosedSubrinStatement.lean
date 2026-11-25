module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralClosureOfFiniteMapIntegrallyClosedSubrin
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.integralClosure_of_finite_map_integrallyClosed_subrings : ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) (B' : Subalgebra k L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.Finite → IsIntegrallyClosed B → IsIntegrallyClosed B' → (∀ x : K, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) → (∀ y : L, ∃ a ∈ B', ∃ b ∈ B', b ≠ 0 ∧ y * b = a) → (∀ y ∈ B', IsIntegral B (y : L)) ∧ (∀ x : K, IsIntegral B x → x ∈ B) ∧ (∀ y : L, IsIntegral B y → y ∈ B') := by
  first | (exact @GlobalTheory.W1.integralClosure_of_finite_map) | (exact GlobalTheory.W1.integralClosure_of_finite_map) | (intros; apply GlobalTheory.W1.integralClosure_of_finite_map  <;> assumption)
