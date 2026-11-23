module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitFrame

open GlobalTheory.IdemModTwo (fj inF inF_finPart inF_tmul)
open GlobalTheory.SplitHeckeLabel (exists_local_lattice smul_mem_latHat mul_mem_intA intA)

theorem exists_gl_of_lattice (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {K : Type} [Field K]
    [Algebra O K] [IsFractionRing O K] {n : ℕ} (Λ : Submodule O (Fin n → K)) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ β : GL (Fin n) K, ∀ w, w ∈ Λ ↔ ∀ i, IsInt O (((β⁻¹).1 *ᵥ w) i) := by
  classical
  have : Submodule.IsFullLattice K Λ := { toIsLattice := Submodule.IsLattice.of_fg K hfg, span_eq_top := hsp }
  have := Submodule.IsLattice.finite K Λ
  have := Submodule.IsLattice.free K Λ
  have hr : Module.finrank O Λ = n := by
    rw [((Submodule.IsFullLattice.finrank_eq K Λ).trans (Module.finrank_fintype_fun_eq_card K)), Fintype.card_fin]
  let b : Module.Basis (Fin n) O Λ := Module.finBasisOfFinrankEq O Λ hr
  let c : Module.Basis (Fin n) K (Fin n → K) := b.extendOfIsFullLattice K
  let s := Pi.basisFun K (Fin n)
  refine ⟨⟨s.toMatrix c, c.toMatrix s, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩, fun w => ?_⟩
  have hw : c.toMatrix s *ᵥ w = c.repr w := by
    exact Module.Basis.toMatrix_mulVec_repr s c w
  change _ ↔ ∀ i, IsInt O ((c.toMatrix s *ᵥ w) i)
  rw [hw]
  have hc : ∀ i, c i = (b i : Fin n → K) := fun i => Module.Basis.extendOfIsFullLattice_apply K b i
  constructor
  · intro h i
    refine ⟨b.repr ⟨w, h⟩ i, ?_⟩
    have h1 : w = ∑ j, algebraMap O K (b.repr ⟨w, h⟩ j) • c j := by
      have := congrArg Subtype.val (b.sum_repr ⟨w, h⟩)
      rw [Submodule.coe_sum] at this
      refine this.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [hc, algebraMap_smul]
      rfl
    conv_rhs => rw [h1]
    rw [c.repr_sum_self]
  · intro h
    choose o ho using h
    rw [← c.sum_repr w]
    refine Λ.sum_mem fun j _ => ?_
    rw [← ho, algebraMap_smul, hc]
    exact Λ.smul_mem _ (b j).2

variable {D : D7}

theorem finPart_inF (z : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (inF D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [AddMonoidHom.map_zero, RingHom.map_zero]
  | tmul a x => rfl
  | add x y hx hy => rw [AddMonoidHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem exists_factor {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (h : Chart e v π) : ∃ φ : Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v, ∀ z, φ (finPart D z) = π z := by
  have h1 : π (fj D 1) = 1 := (h.2.2.1 _).trans (map_one (evalV D.host.F v))
  refine ⟨(finPart D).liftOfRightInverse (inF D) finPart_inF ⟨π, fun z hz => ?_⟩, fun z =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ z⟩
  rw [RingHom.mem_ker] at hz ⊢
  have h2 := inF_finPart z
  rw [hz, AddMonoidHom.map_zero] at h2
  have h3 := congrArg π h2
  rwa [RingHom.map_zero, RingHom.map_mul, h1, one_mul, eq_comm] at h3

theorem finPart_mul_eq {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (h : Chart e v π) {φ : Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v} (hφ : ∀ z, φ (finPart D z) = π z)
    (y : AE D) (z : Af D.host.F ⊗[D.host.F] D.host.E) (hy : π y = φ z) : finPart D (e * y) = finPart D e * z := by
  have h1 : π y = π (inF D z) := by
    rw [← hφ (inF D z), finPart_inF]
    exact hy
  have h2 := (h.2.1 (y - inF D z)).1 (by rw [RingHom.map_sub, h1, sub_self])
  rw [mul_sub, sub_eq_zero] at h2
  rw [h2, RingHom.map_mul, finPart_inF]

theorem exists_frame : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ V : HSp D, ∃ β : GL (Fin V.rank) (Fv D.host.F v), Frame V e π β := by
  intro D e v π he h V
  obtain ⟨φ, hφ⟩ := exists_factor h
  have hei : finPart D e ∈ intA D.host.F D.host.E :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he.1])
  have hπe : π e = 1 := by
    have := (h.2.1 (e - 1)).2 (by rw [mul_sub, he.1, mul_one, sub_self])
    rwa [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
    V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := Set.ext fun y => by
    change _ ↔ ∑ i, y i • V.frame i ∈ V.L0
    rw [← V.frame.equivFun_symm_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change V.frame.equivFun.symm (V.frame.equivFun x) ∈ V.L0
      rwa [LinearEquiv.symm_apply_apply]
    · exact fun h => ⟨_, h, V.frame.equivFun.apply_symm_apply y⟩
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    classical
    have hs : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      exact V.span_baseLattice_eq_top
    change Submodule.span _ (V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V)) = ⊤
    rw [← Submodule.map_span, hs, Submodule.map_top, LinearEquiv.range]
  obtain ⟨Λ, hfg, hΛ, hmem⟩ := exists_local_lattice (F := D.host.F) L (V.standardTuple_isLattice.fg.map _) hsp v φ
    (fun a => (hφ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 a))).trans (h.2.2.1 _))
    (fun x hx => by
      rw [← finPart_inF x, hφ, ← isInt_Ov, ← h.2.2.2, RingHom.map_mul, finPart_inF]
      exact mul_mem_intA hei hx)
  obtain ⟨β, hβ⟩ := exists_gl_of_lattice (Ov D v) Λ hfg hΛ
  refine ⟨β, fun y => ?_⟩
  rw [← hβ, hmem, LamHat, ← hL]
  constructor
  · intro hy
    refine ⟨_, hy, funext fun i => ?_⟩
    rw [Function.comp_apply, hφ, RingHom.map_mul, hπe, one_mul]
  · rintro ⟨z, hz, hy⟩
    have : (fun i => finPart D (e * y i)) = finPart D e • z := funext fun i =>
      finPart_mul_eq h hφ (y i) (z i) (congrFun hy i)
    rw [this]
    exact smul_mem_latHat L hei hz

end GlobalTheory.SplitFrame

end
