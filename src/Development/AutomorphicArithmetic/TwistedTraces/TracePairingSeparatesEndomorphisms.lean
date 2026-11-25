module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Trace
import Development.AutomorphicArithmetic.TwistedTraces.LinearFormEqMulTraceOfTwistedInvariant
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped BigOperators

open TensorProduct in
private lemma commuting_idempotent_trace {X : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] :
    ∀ (r : ℕ) (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)]
      [∀ i, FiniteDimensional ℂ (S i)] [∀ i, Nontrivial (S i)]
      (c : ∀ i, Module.End ℂ (S i) →ₐ[ℂ] Module.End ℂ X),
      (∀ i j, i ≠ j → ∀ s t, Commute (c i s) (c j t)) →
      ∀ B : Module.End ℂ X, IsIdempotentElem B → (∀ i s, Commute B (c i s)) →
      ∃ N : ℕ, ∀ t : ∀ i, Module.End ℂ (S i),
        LinearMap.trace ℂ X (B * (List.ofFn fun i => c i (t i)).prod)
          = N * ∏ i, LinearMap.trace ℂ (S i) (t i) := by
  intro r
  induction r with
  | zero =>
    intro S _ _ _ _ c hc B hB hcomm
    refine ⟨Module.finrank ℂ (LinearMap.range B), fun t => ?_⟩
    have := (LinearMap.IsIdempotentElem.isProj_range B hB).trace
    simpa using this
  | succ r ih =>
    intro S _ _ _ _ c hc B hB hcomm
    obtain ⟨e, he⟩ := exists_ne (0 : S 0)
    obtain ⟨ξ, h1⟩ := Module.Projective.exists_dual_eq_one ℂ he
    set E : Module.End ℂ (S 0) := dualTensorHom ℂ (S 0) (S 0) (ξ ⊗ₜ e) with hEdef
    have hE : IsIdempotentElem E := by
      show E * E = E
      ext y
      simp [hEdef, dualTensorHom_apply, h1]
    have hB' : IsIdempotentElem (B * c 0 E) :=
      IsIdempotentElem.mul_of_commute (hcomm 0 E) hB (hE.map (c 0))
    have hcomm' : ∀ (i : Fin r) (s : Module.End ℂ (S i.succ)),
        Commute (B * c 0 E) (c i.succ s) := fun i s =>
      (hcomm i.succ s).mul_left (hc 0 i.succ (Fin.succ_ne_zero i).symm E s)
    obtain ⟨N, hN⟩ := ih (fun i => S i.succ) (fun i => c i.succ)
      (fun i j hij s t => hc i.succ j.succ (fun h => hij (Fin.succ_injective _ h)) s t)
      (B * c 0 E) hB' hcomm'
    refine ⟨N, fun t => ?_⟩
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    set A : Module.End ℂ X := (List.ofFn fun i : Fin r => c i.succ (t i.succ)).prod with hA
    have hAc : ∀ s, Commute (c 0 s) A := fun s => by
      refine Commute.list_prod_right _ _ ?_
      intro x hx
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact hc 0 i.succ (Fin.succ_ne_zero i).symm s _
    let τ : Module.End ℂ (S 0) →ₗ[ℂ] ℂ :=
      (LinearMap.trace ℂ X) ∘ₗ (LinearMap.mulRight ℂ A) ∘ₗ (LinearMap.mulLeft ℂ B) ∘ₗ
        (c 0).toLinearMap
    have hτv : ∀ s, τ s = LinearMap.trace ℂ X (B * c 0 s * A) := fun s => rfl
    have hτ : ∀ a b, τ (a * b) = τ (b * a) := by
      intro a b
      simp only [hτv, map_mul, mul_assoc]
      rw [(hcomm 0 a).left_comm, LinearMap.trace_mul_comm]
      simp only [mul_assoc]
      rw [← (hAc a).eq]
    have key := UpperTheory.linearForm_eq_mul_trace_of_twisted_invariant (S 0) 1 E τ
      (by simpa [hEdef, LinearMap.trace_eq_contract_apply, contractLeft_apply] using h1)
      (fun a a' b ha => by simp only [mul_one, one_mul] at ha; simpa [ha] using hτ b a) (t 0)
    simp only [mul_one] at key
    have hN' := hN (fun i => t i.succ)
    rw [← mul_assoc, ← hτv, key, hτv, hN']
    ring

theorem UpperTheory.trace_pairing_separates_endomorphisms :
    ∀ (r : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] [∀ i, FiniteDimensional ℂ (S i)] [∀ i, Nontrivial (S i)] (c : ∀ i, Module.End ℂ (S i) →ₐ[ℂ] Module.End ℂ X), (∀ i j, i ≠ j → ∀ s t, Commute (c i s) (c j t)) → ∃ N : ℕ, ∀ t : ∀ i, Module.End ℂ (S i), LinearMap.trace ℂ X (List.ofFn fun i => c i (t i)).prod = N * ∏ i, LinearMap.trace ℂ (S i) (t i) := by
  intro r X _ _ _ S _ _ _ _ c hc
  obtain ⟨N, hN⟩ := commuting_idempotent_trace r S c hc 1 IsIdempotentElem.one (fun _ _ => Commute.one_left _)
  exact ⟨N, fun t => by simpa using hN t⟩
