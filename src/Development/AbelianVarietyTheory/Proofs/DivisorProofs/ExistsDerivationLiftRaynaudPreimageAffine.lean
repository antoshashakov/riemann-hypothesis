module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDerivationExtendOfFormallySmooth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoExtendsSemiAbelianDvrInducingFormal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageProjectionAbelianPart

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LiftDer

theorem exists_lift_of_smooth (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) [Smooth f]
    (U : X.Opens) (hU : IsAffineOpen U) (D : Derivation ℤ R R) :
    ∃ δ : Γ(X, U) → Γ(X, U), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧
      ∀ r, δ (constFn f U r) = constFn f U (D r) := by
  let g : R →+* Γ(X, U) :=
    (f.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hg : g.Smooth := by
    refine RingHom.Smooth.comp (RingHom.Smooth.of_bijective ?_) ?_
    · exact ((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm).bijective
    · exact HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  letI : Algebra R Γ(X, U) := g.toAlgebra
  haveI : Algebra.FormallySmooth R Γ(X, U) := hg.formallySmooth
  obtain ⟨d, hadd, hmul, hc⟩ := GlobalTheory.KS.exists_derivation_extend_of_formallySmooth R Γ(X, U) Γ(X, U)
    (RingHom.id _) (fun r => g (D r)) (fun a b => by simp) (fun a b => by
      simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, RingHom.id_apply]
      rw [RingHom.algebraMap_toAlgebra])
  exact ⟨d, hadd, hmul, fun r => hc r⟩

theorem isAffineHom_q {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) : IsAffineHom Y.q.left :=
  GlobalTheory.RayEv.Ray.isAffineHom_q Y

theorem smooth_H {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) : Smooth Y.H.hom := by
  have h1 : Smooth Y.q.left := Y.smooth_q
  have := Q.P.smoothDim
  have h2 : Smooth Q.P.A.hom := SmoothOfRelativeDimension.smooth Q.P.g _
  rw [← Over.w Y.q]
  infer_instance

theorem exists_lift_preimage : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ δ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ ∀ r, δ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r) := by
  intro R _ _ Q O _ _ _ oa Y V D
  have := isAffineHom_q Y
  have := smooth_H Y
  exact exists_lift_of_smooth R Y.H.left Y.H.hom _ (V.2.preimage Y.q.left) D

end GlobalTheory.LiftDer
