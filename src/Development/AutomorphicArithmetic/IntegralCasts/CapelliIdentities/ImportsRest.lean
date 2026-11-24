module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
import Supplements.MathlibImports.AnalysisAndTactics
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

theorem UpperTheory.Reformulated.B.DYha2.main :
    ∀ {X Y : Type} [inst : AddCommGroup X] [inst_1 : _root_.Module ℂ X] [inst_2 : AddCommGroup Y]
      [inst_3 : _root_.Module ℂ Y] {x : X} {y : Y}, x ≠ (0 : X) → y ≠ (0 : Y) → x ⊗ₜ[ℂ] y ≠ (0 : TensorProduct ℂ X Y) := by
  intro X Y _ _ _ _ x y hx hy h
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ hx
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero ℂ hy
  have key := congrArg (TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ f g)) h
  simp only [TensorProduct.lift.tmul, map_zero, LinearMap.compl₁₂_apply, LinearMap.mul_apply'] at key
  exact (mul_ne_zero hf hg) key
