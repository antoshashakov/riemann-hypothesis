module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeDifferentOrderBoundedAbsoluteRamificatio
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CompIntField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

theorem _root_.GlobalTheory.T.relative_different_order_bounded_absolute_ramification : ∀ (l e : ℕ), l.Prime → ∃ c : ℕ, ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L)), la.asIdeal.under (𝓞 K) = p.asIdeal → ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → ((l : ℕ) : 𝓞 L) ∉ la.asIdeal ^ (e + 1) → ¬ la.asIdeal ^ (c + 1) ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  first | exact @GlobalTheory.TowerDifferent.relDifferent_order_bounded | exact GlobalTheory.TowerDifferent.relDifferent_order_bounded | (intros; apply GlobalTheory.TowerDifferent.relDifferent_order_bounded <;> assumption)
