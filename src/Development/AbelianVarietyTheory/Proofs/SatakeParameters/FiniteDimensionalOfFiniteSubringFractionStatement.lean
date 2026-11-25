module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalOfFiniteSubringFraction
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.finiteDimensional_of_finite_subring_hom_of_fractions : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (B : Subring K) (B' : Subring L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.Finite → (∀ y : L, ∃ a ∈ B', ∃ b ∈ B', b ≠ 0 ∧ y * b = a) → FiniteDimensional K L := by
  first | (exact @GlobalTheory.finiteDimensional_of_finite_subring_fraction) | (exact GlobalTheory.finiteDimensional_of_finite_subring_fraction) | (intros; apply GlobalTheory.finiteDimensional_of_finite_subring_fraction  <;> assumption)
