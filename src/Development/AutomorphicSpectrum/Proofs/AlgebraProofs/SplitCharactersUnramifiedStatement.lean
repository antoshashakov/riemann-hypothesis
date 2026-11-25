module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SplitCharactersUnramified
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.split_characters_unramified : ∀ (E : Type) [Field E] [NumberField E] (R K S : Type) [CommRing R] [IsDomain R] [CharZero R] [Field K] [Fintype S] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] (σ : S → (𝓞 E →+* R)) (π : R →+* K), Function.Injective σ → Fintype.card S = Module.finrank ℚ E → ¬ (p : ℤ) ∣ NumberField.discr E → ∃ χ : S → (𝓞 E →+* algebraicClosure (ZMod p) K), IsSplit χ ∧ ∀ s a, ((χ s a : algebraicClosure (ZMod p) K) : K) = π (σ s a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc.exists_isSplit | exact GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc.exists_isSplit | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc.exists_isSplit <;> assumption)
