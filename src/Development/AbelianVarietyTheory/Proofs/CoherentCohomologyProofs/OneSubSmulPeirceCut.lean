module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Idempotent
import Supplements.MathlibImports.AnalysisAndTactics
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.Algebra.Ring.Idempotent

@[expose] public section

namespace GlobalTheory.PeirceDecompositionCut

variable {R : Type*} [CommRing R] (A : Type*) [Ring A] [Algebra R A]

def peirceCut (e : R) (he : IsIdempotentElem e) : A →* A where
  toFun x := e • x + (1 - e) • (1 : A)
  map_one' := by rw [← add_smul, add_sub_cancel, one_smul]
  map_mul' x y := by
    have h1 : e * e = e := he
    have h2 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, h1, sub_self]
    have h3 : (1 - e) * e = 0 := by rw [mul_comm, h2]
    have h4 : (1 - e) * (1 - e) = 1 - e := he.one_sub
    simp only [add_mul, mul_add, smul_mul_smul_comm, h1, h2, h3, h4, zero_smul, add_zero,
      zero_add, mul_one]

variable {A}

end GlobalTheory.PeirceDecompositionCut
