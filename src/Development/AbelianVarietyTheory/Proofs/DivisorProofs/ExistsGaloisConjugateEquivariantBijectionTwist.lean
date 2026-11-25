module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecTw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFramePullbackMumfordFrameGaloisTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OperatorRelationPullbackGaloisAutomorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistChartAdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistFixesIntegralFamil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistSemilinearSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartAdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartSemilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistIsConjugate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLiftGaloisTwistOfConjugatePoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupActionPullbackThetaSectionsGaloisTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UwRQeIsNsmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


open GlobalTheory.Mum GlobalTheory.Mum.Conj in
theorem GlobalTheory.Mum.exists_eqv_conj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E, Eqv D.toPre A (Kb R) N lab E → (∀ τ : Kb R →ₐ[FractionRing R] Kb R, LabExt τ lab lab) → ∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ E', Eqv D.toPre A (Kb R) N lab E' ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre N) s, F₀.Over s → SecTw σ (E s) (E' s) := by
  intro R _ _ _ _ D A N _ lab E hE hlab σ
  have hσ : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  let σe : Kb R ≃ₐ[FractionRing R] Kb R := AlgEquiv.ofBijective σ hσ
  let τ : Kb R →ₐ[FractionRing R] Kb R := σe.symm.toAlgHom
  have hστ : σ.comp τ = AlgHom.id _ _ := AlgHom.ext fun x => σe.apply_symm_apply x
  have hστ' : ∀ x, σ (τ x) = x := fun x => σe.apply_symm_apply x
  refine ⟨fun s => secTw A N σ (E (famTw D.toPre N τ s)), ⟨?_, ?_, ?_, hE.onto, hE.frame, hE.lift, ?_⟩, ?_⟩
  · exact (_root_.GlobalTheory.Mum.Conj.secTw_bijective R A N σ).comp (hE.bij.comp (_root_.GlobalTheory.Mum.Conj.FamBij.famTw_bijective R D.toPre N τ))
  · intro s s' s'' h j
    exact _root_.GlobalTheory.Mum.Conj.secTw_add_chart R A N σ _ _ _ (hE.add _ _ _ (_root_.GlobalTheory.Mum.Conj.famTw_add_f R D.toPre N τ _ _ _ h)) j
  · intro c s s' h j
    have := _root_.GlobalTheory.Mum.Conj.secTw_chart_smul R A N σ (τ c) _ _ (hE.smul (τ c) _ _ (_root_.GlobalTheory.Mum.Conj.famTw_isSmul R D.toPre N τ c _ _ h)) j
    rwa [hστ'] at this
  · intro p w θ s s' hw hθ hφ
    obtain ⟨p₀, hp₀⟩ := qkExtExists R D.toPre (Kb R) (Kb R) τ.toRingHom (fun r => τ.commutes r) N p
    have hx := hlab τ p p₀ hp₀
    exact _root_.GlobalTheory.Mum.Conj.isActOf_secTw R A N σ τ hστ θ _ _ (hE.act p₀ (frTw D.toPre τ hp₀ w) (thTw A N τ θ) _ _
      (_root_.GlobalTheory.Mum.Conj.txFrame_frTw R D.toPre N τ p p₀ hp₀ w hw) (_root_.GlobalTheory.Mum.Conj.symLift_thTw R A N τ _ _ θ hθ hx) (_root_.GlobalTheory.Mum.Conj.PhiTw.phiRel_famTw R D.toPre N τ p p₀ hp₀ w s s' hφ))
  · intro F₀ s hs
    show SecTw σ (E s) (secTw A N σ (E (famTw D.toPre N τ s)))
    rw [_root_.GlobalTheory.Mum.Conj.famTw_eq_of_over R _ D.toPre N τ F₀ s hs]
    exact _root_.GlobalTheory.Mum.Conj.secTw_isTwist R A N σ (E s)
