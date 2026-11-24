module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankKerMapLeOfFirstOrderKernelExt
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.finrank_ker_map_le_of_first_order_kernel_ext : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (a e : ℕ) (Φ : Matrix (Fin a) (Fin a) k) (U : Type) [AddCommGroup U] [Module k U] [Module.Finite k U] (t u : LinearMap.ker Φ.mulVecLin →ₗ[k] U), (∀ x0 x1 : Fin (e + 1) → LinearMap.ker Φ.mulVecLin, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → Module.finrank K (LinearMap.ker (Φ.map (algebraMap k K)).mulVecLin) ≤ Module.finrank k U + e := by
  first | exact @GlobalTheory.finrank_ker_map_le_of_first_order_kernel | exact GlobalTheory.finrank_ker_map_le_of_first_order_kernel | (intros; apply GlobalTheory.finrank_ker_map_le_of_first_order_kernel <;> assumption)
