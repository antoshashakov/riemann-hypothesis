module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFibreProjectiveEmbedding
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.generic_fibre_projective_embedding : ∀ (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)), IsProjOver s → Tor.IsNormalScheme P → IsReduced (pullback s (spMap (algebraMap (𝓞 F) F))) ∧ IsLocallyNoetherian (pullback s (spMap (algebraMap (𝓞 F) F))) ∧ ∃ (M : ℕ) (i : pullback s (spMap (algebraMap (𝓞 F) F)) ⟶ PSpace F M), IsClosedImmersion i ∧ i ≫ PSpace.str F M = pullback.snd _ _ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.genericFibre_reduced_noetherian_closed | exact GlobalTheory.CompanionTheory.Ar.SncBase.genericFibre_reduced_noetherian_closed | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.genericFibre_reduced_noetherian_closed <;> assumption)
