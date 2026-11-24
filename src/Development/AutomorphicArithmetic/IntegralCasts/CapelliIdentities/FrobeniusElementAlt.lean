module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Nat.Prime.Defs
import Supplements.MathlibImports.AnalysisAndTactics
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.CharP.Lemmas

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.FrobeniusElementAlt.frb :
    {l : ℕ} → [Fact (Nat.Prime l)] → {B : Type} → [inst : CommRing B] → (↑l : B) = (0 : B) → B →+* B :=
  fun {l} hl {B} _ h =>
    { toFun := fun x => x ^ l
      map_one' := one_pow l
      map_mul' := fun x y => mul_pow x y l
      map_zero' := zero_pow hl.out.ne_zero
      map_add' := fun x y => by
        rw [add_pow_prime_eq hl.out x y, h]
        simp }
