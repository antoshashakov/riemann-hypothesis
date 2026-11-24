module

public import Mathlib.Data.Matrix.Basic
import Supplements.MathlibImports.AnalysisAndTactics
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Data.Matrix.Basis

@[expose] public section

namespace UpperTheory.Reformulated.B.Qi38

noncomputable def Irr : {R : Type} →
  [inst : CommRing R] →
    {H : Type} →
      [inst_1 : Group H] → {n : Type} → [inst_2 : Fintype n] → [inst_3 : DecidableEq n] → (H →* Matrix n n R) → Prop :=
  fun {R} [CommRing R] {H} [Group H] {n} [Fintype n] [DecidableEq n] r => Submodule.span R (Set.range ⇑r) = ⊤

@[reducible] noncomputable def modFun : {O M ι : Type} →
  [inst : CommRing O] → [inst_1 : AddCommGroup M] → [Module O M] → Module O (ι → M) :=
  fun {O M ι} [CommRing O] [AddCommGroup M] [Module O M] => Pi.Function.module ι O M

attribute [local instance] modFun

noncomputable def mapRep : {R R' : Type} →
  [inst : CommRing R] →
    [inst_1 : CommRing R'] →
      {H : Type} →
        [inst_2 : Group H] →
          {n : Type} →
            [inst_3 : Fintype n] → [inst_4 : DecidableEq n] → (R →+* R') → (H →* Matrix n n R) → H →* Matrix n n R' :=
  fun {R R'} [CommRing R] [CommRing R'] {H} [Group H] {n} [Fintype n] [DecidableEq n] f r => f.mapMatrix.toMonoidHom.comp r

private theorem aux {Γ E E' : Type} [Field E] [Field E'] (f : E →+* E') {n : Nat}
    (r : Γ → Matrix (Fin n) (Fin n) E) (hr : Submodule.span E (Set.range r) = ⊤)
    (N : Submodule E' (Fin n → E'))
    (hN : ∀ g v, v ∈ N → ((r g).map f).mulVec v ∈ N) : N = ⊥ ∨ N = ⊤ := by
  have key : ∀ A : Matrix (Fin n) (Fin n) E, ∀ v ∈ N, (A.map f).mulVec v ∈ N := by
    intro A v hv
    have hA : A ∈ Submodule.span E (Set.range r) := by rw [hr]; exact Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hN g v hv
    | zero =>
      rw [Matrix.map_zero _ (map_zero f), Matrix.zero_mulVec]
      exact N.zero_mem
    | add x y _ _ hx hy =>
      rw [Matrix.map_add _ (map_add f), Matrix.add_mulVec]
      exact N.add_mem hx hy
    | smul a x _ hx =>
      have h : (a • x).map f = f a • x.map f := by
        ext i j
        simp
      rw [h, Matrix.smul_mulVec]
      exact N.smul_mem _ hx
  refine or_iff_not_imp_left.2 fun hne => ?_
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff N).1 hne
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
  have hj' : v j ≠ 0 := hj
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine N.sum_mem fun i _ => ?_
  have h1 := N.smul_mem (w i * (v j)⁻¹) (key (Matrix.single i j 1) v hv)
  have h2 : (w i * (v j)⁻¹) • ((Matrix.single i j (1 : E)).map f).mulVec v = Pi.single i (w i) := by
    rw [Matrix.map_single, map_one, Matrix.single_mulVec]
    ext k
    by_cases hk : k = i
    · subst hk
      simp [hj']
    · simp [hk]
  rwa [h2] at h1

theorem irr_map : ∀ {Γ E E' : Type} [inst : Group Γ] [inst_1 : Field E]
  [inst_2 : Field E'] (f : E →+* E') {n : ℕ} (r : Γ →* Matrix (Fin n) (Fin n) E),
  Irr r →
    ∀ (N : Submodule E' (Fin n → E')),
      (∀ (g : Γ), ∀ v ∈ N, ((mapRep f r) g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro Γ E E' _ _ _ f n r hr N hN
  exact aux f (fun g => r g) hr N hN

end UpperTheory.Reformulated.B.Qi38
