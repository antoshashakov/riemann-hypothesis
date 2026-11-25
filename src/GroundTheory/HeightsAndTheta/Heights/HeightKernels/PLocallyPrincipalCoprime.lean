module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLocallyPrincipalCoprime
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace LocallyPrincipalCoprimeAlt

variable {L : Type} [Field L]

theorem finite_maximal_of_ne_zero [CharZero L] (B : Subring L) [Module.Finite ℤ B] {s : B} (hs : s ≠ 0) :
    Set.Finite {m : Ideal B | m.IsMaximal ∧ s ∈ m} := by
  have : Ring.HasFiniteQuotients B := Ring.HasFiniteQuotients.of_module_finite ℤ B
  exact (Ring.HasFiniteQuotients.finite_setOfPred_mem s hs).subset fun _ hm => hm.2

theorem mem_span_of_local {B : Subring L} {M : AddSubgroup L} {ι : Type} {a : ι → L}
    (hloc : ∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i)
    {z : L} (hz : z ∈ M) : z ∈ Submodule.span B (Set.range a) := by
  let S := Submodule.span B (Set.range a)
  by_contra hzS
  have hJ : S.colon {z} ≠ ⊤ := by simpa using hzS
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal _ hJ
  obtain ⟨i, hi⟩ := hloc m hm
  obtain ⟨b, c, hbm, hbc⟩ := hi z hz
  apply hbm (hJm (Submodule.mem_colon_singleton.mpr ?_))
  change (b : L) * z ∈ S
  rw [hbc]
  exact S.smul_mem c (Submodule.subset_span ⟨i, rfl⟩)

theorem ne_zero_of_local {B : Subring L} {M : AddSubgroup L} {ι : Type} {a : ι → L} {m : Ideal B} {i : ι}
    (hi : ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i) (hM : M ≠ ⊥) : a i ≠ 0 := by
  obtain ⟨⟨z, hz⟩, hz0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hM
  obtain ⟨b, c, hbm, hbc⟩ := hi z hz
  have hb : (b : L) ≠ 0 := fun e => hbm ((show b = 0 from Subtype.ext e).symm ▸ m.zero_mem)
  have hz0' : z ≠ 0 := fun e => hz0 (Subtype.ext e)
  exact fun e => mul_ne_zero hb hz0' (by simpa only [e, mul_zero] using hbc)

theorem exists_local_mult {B : Subring L} {M : AddSubgroup L} {ι : Type} [Fintype ι] {a : ι → L}
    (haM : ∀ i, a i ∈ M)
    (hloc : ∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i)
    (hM : M ≠ ⊥) (m : Ideal B) (hm : m.IsMaximal) :
    ∃ (g : L) (i : ι), (∀ z ∈ M, g * z ∈ B) ∧ ∃ y : B, (y : L) = g * a i ∧ y ∉ m := by
  obtain ⟨i, hi⟩ := hloc m hm
  have hai := ne_zero_of_local hi hM
  let P := Submodule.span B {a i}
  have hK : ¬ (Finset.univ.inf fun j => P.colon {a j}) ≤ m := by
    rw [hm.isPrime.inf_le']
    rintro ⟨j, -, hj⟩
    obtain ⟨b, c, hbm, hbc⟩ := hi (a j) (haM j)
    exact hbm (hj (Submodule.mem_colon_singleton.mpr
      (Submodule.mem_span_singleton.mpr ⟨c, hbc.symm⟩)))
  obtain ⟨t, htK, htm⟩ := IsConcreteLE.not_le_iff_exists.mp hK
  refine ⟨t / a i, i, fun z hz => ?_, t, by field_simp, htm⟩
  have hle : Submodule.span B (Set.range a) ≤ P.comap (t • LinearMap.id) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact Submodule.mem_colon_singleton.mp
      ((Finset.inf_le (f := fun j => P.colon {a j}) (Finset.mem_univ j)) htK)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hle (mem_span_of_local hloc hz))
  change (c : L) * a i = (t : L) * z at hc
  rw [div_mul_eq_mul_div, ← hc, mul_div_cancel_right₀ _ hai]
  exact c.2


open scoped Classical in
open Classical in
noncomputable def toB (B : Subring L) (x : L) : B := if h : x ∈ B then ⟨x, h⟩ else 0

theorem coe_toB {B : Subring L} {x : L} (h : x ∈ B) : (toB B x : L) = x := by
  simp [toB, h]

end LocallyPrincipalCoprimeAlt


open LocallyPrincipalCoprimeAlt in
theorem LocallyPrincipalCoprime.proof : LocallyPrincipalCoprime.Statement := by
  classical
  intro L _ _ B M ι _ a hfin hBM haM hden hloc hM s hs
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal B
  have : Nonempty ι := ⟨(hloc m₀ hm₀).choose⟩
  choose! g idx hgM y hy hym using exists_local_mult haM hloc hM
  have hS := finite_maximal_of_ne_zero B hs
  set S := hS.toFinset with hSdef
  have memS : ∀ m, m ∈ S ↔ m.IsMaximal ∧ s ∈ m := fun m => hS.mem_toFinset

  have hy0 : (y m₀ : L) ≠ 0 := fun h => hym m₀ hm₀
    ((show y m₀ = 0 from Subtype.ext h).symm ▸ m₀.zero_mem)
  have ha0 : a (idx m₀) ≠ 0 := fun h => hy0 (by rw [hy m₀ hm₀, h, mul_zero])
  have hg0 : g m₀ ≠ 0 := fun h => hy0 (by rw [hy m₀ hm₀, h, zero_mul])
  obtain ⟨γ, hγM, hγ, hγm⟩ : ∃ γ : L, (∀ z ∈ M, γ * z ∈ B) ∧ γ ≠ 0 ∧
      ∀ m ∈ S, ∀ h : γ * a (idx m) ∈ B, (⟨_, h⟩ : B) ∉ m := by
    rcases S.eq_empty_or_nonempty with hS | ⟨m, hm⟩
    · exact ⟨g m₀, hgM m₀ hm₀, hg0, by simp [hS]⟩
    let D : Submodule B L :=
      { carrier := {d | ∀ z ∈ M, d * z ∈ B}
        zero_mem' := by simp
        add_mem' := fun {u v} hu hv z hz => by
          rw [add_mul]
          exact B.add_mem (hu z hz) (hv z hz)
        smul_mem' := fun b u hu z hz => by
          change (b : L) * u * z ∈ B
          rw [mul_assoc]
          exact B.mul_mem b.2 (hu z hz) }
    let p : S → Ideal B := Subtype.val
    have hp : Pairwise fun i j => IsCoprime (p i) (p j) := fun i j hij =>
      Ideal.isCoprime_iff_sup_eq.mpr <|
        ((memS i).mp i.2).1.coprime_of_ne ((memS j).mp j.2).1 (fun e => hij (Subtype.ext e))
    let d (j : S) : D := ⟨g j, hgM j ((memS j).mp j.2).1⟩
    obtain ⟨w, hw⟩ := Ideal.pi_tensorProductMk_quotient_surjective D p hp
      (fun j => TensorProduct.mk B (B ⧸ p j) D 1 (d j))
    let eval (j : S) : D →ₗ[B] B :=
      { toFun := fun u => ⟨(u : L) * a (idx j), u.2 _ (haM _)⟩
        map_add' := fun u v => Subtype.ext (add_mul _ _ _)
        map_smul' := fun b u => Subtype.ext (mul_assoc _ _ _) }
    have heval (j : S) : Ideal.Quotient.mk (p j) (eval j w) =
        Ideal.Quotient.mk (p j) (y j) := by
      have hj := congrArg ((TensorProduct.rid B (B ⧸ p j)) ∘
        (eval j).lTensor (B ⧸ p j)) (congrFun hw j)
      have hyj : eval j (d j) = y j := Subtype.ext (hy j ((memS j).mp j.2).1).symm
      simpa only [LinearMap.pi_apply, Function.comp_apply, TensorProduct.mk_apply,
        LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Algebra.smul_def, mul_one,
        Ideal.Quotient.algebraMap_eq, hyj] using hj
    have hwm (j : Ideal B) (hj : j ∈ S) (h : (w : L) * a (idx j) ∈ B) :
        (⟨_, h⟩ : B) ∉ j := fun hmem =>
      hym j ((memS j).mp hj).1 (Ideal.Quotient.eq_zero_iff_mem.mp
        ((heval ⟨j, hj⟩).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)))
    refine ⟨(w : L), w.2, ?_, hwm⟩
    intro h
    apply hwm m hm (w.2 _ (haM (idx m)))
    have hzero : (⟨_, w.2 _ (haM (idx m))⟩ : B) = 0 := Subtype.ext (by simp [h])
    exact hzero.symm ▸ m.zero_mem
  obtain ⟨c₀, hc₀B, hc₀, hc₀a⟩ := hden (idx m₀)
  set a₀ := a (idx m₀)
  let N : Submodule B L := { M with smul_mem' := fun b _ hz => hBM b b.2 _ hz }
  let I : Ideal B := N.comap (LinearMap.toSpanSingleton B L γ⁻¹)
  have memI (w : B) : w ∈ I ↔ (w : L) * γ⁻¹ ∈ M := Iff.rfl
  have cancel (x : L) : γ * x * γ⁻¹ = x := by
    rw [mul_comm γ x, mul_assoc, mul_inv_cancel₀ hγ, mul_one]
  let δ : B := ⟨c₀ * a₀, hc₀a⟩
  let β : B := ⟨(δ : L) * γ, by
    change c₀ * a₀ * γ ∈ B
    rw [mul_assoc, mul_comm a₀ γ]
    exact B.mul_mem hc₀B (hγM _ (haM _))⟩
  have hδ : (δ : L) ≠ 0 := mul_ne_zero hc₀ ha0
  refine ⟨β, δ, I, fun h => mul_ne_zero hδ hγ (congrArg Subtype.val h),
    fun h => hδ (congrArg Subtype.val h), ?_, ?_⟩
  · by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    have hmS := (memS m).mpr ⟨hm, hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))⟩
    have hmem : (⟨_, hγM _ (haM (idx m))⟩ : B) ∈ I := by
      rw [memI, cancel]
      exact haM _
    exact hγm m hmS _ (hle (Ideal.mem_sup_left hmem))
  · intro x
    have hrel (w : B) : (β : L) * x = δ * w ↔ γ * x = w := by
      change (δ : L) * γ * x = δ * w ↔ _
      rw [mul_assoc, mul_right_inj' hδ]
    constructor
    · intro hx
      refine ⟨⟨γ * x, hγM x hx⟩, ?_, (hrel _).mpr rfl⟩
      rwa [memI, cancel]
    · rintro ⟨w, hw, h⟩
      rwa [memI, ← (hrel w).mp h, cancel] at hw

end GroundTheory.Heights₂.Heights
