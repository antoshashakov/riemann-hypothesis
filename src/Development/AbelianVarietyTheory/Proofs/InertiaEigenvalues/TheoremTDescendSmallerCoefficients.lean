module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterSetMapCoefficientFieldProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLatticeBasisLocal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionFiniteExtensionQl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeJumpsMemLatticeCoefficientExtension
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughCharactersLatticeCoefficientExtens
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotentiallyCrystallineLatticeCoefficientExtens
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomBaseChangeOnto
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftableDescendsFromLargerCoefficientField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem thmT_descend : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l), LL.1 ≤ LL'.1 → ∀ C : ℕ, Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL' C → Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL C := by
  intro l _ Pl K' h hN hF hS LL LL' hL C hT
  intro T₁ T₂ F N η H U Sig Fr hp1 hp2 hon hFr hFS h1 hcard h2N hI1 hI2 hU h0U hUc hη hηH hJ1 hJ2 hl
  obtain ⟨k₁, b₁, hb₁⟩ := _root_.GlobalTheory.BaseCoef.lattice_basis_exists l LL T₁
  obtain ⟨k₂, b₂, hb₂⟩ := _root_.GlobalTheory.BaseCoef.lattice_basis_exists l LL T₂
  obtain ⟨r, hr1, hr2, hr3⟩ := _root_.GlobalTheory.CoefRetraction.exists_integral_retraction l LL LL' hL
  obtain ⟨hFS', hrP, hcard', h1'⟩ := _root_.GlobalTheory.BaseCoef.mapSig_props (incl hL).toRingHom (pc Pl h hN hF hS).Iner Fr Sig
  have key := hT (extLat hL T₁ b₁ hb₁) (extLat hL T₂ b₂ hb₂) (extHom hL hb₁ hb₂ F) N η H U
    (mapSig (incl hL).toRingHom Sig) Fr
    (_root_.GlobalTheory.BaseCoef.isPotCrys_extLat l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ hp1) (_root_.GlobalTheory.BaseCoef.isPotCrys_extLat l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ hp2)
    (_root_.GlobalTheory.BaseCoef.extHom_onto l LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F hon) hFr (hFS' hFS) (h1' h1) (hcard'.trans hcard) h2N
    (_root_.GlobalTheory.BaseCoefIner.main l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ Sig hI1) (_root_.GlobalTheory.BaseCoefIner.main l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ Sig hI2)
    hU h0U hUc hη hηH
    (_root_.GlobalTheory.BaseCoef.jumpsInV_extLat l Pl K' h hN hF hS LL LL' hL T₁ k₁ b₁ hb₁ _ hJ1) (_root_.GlobalTheory.BaseCoef.jumpsInV_extLat l Pl K' h hN hF hS LL LL' hL T₂ k₂ b₂ hb₂ _ hJ2) hl
  rw [hrP] at key
  exact ⟨key.1, _root_.GlobalTheory.CoefDescent.liftF_descends l _ LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F r hr1 hr2 hr3 (by haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2; exact LinearMap.continuous_of_finiteDimensional r) _ key.2⟩

end GlobalTheory.BaseCoef
