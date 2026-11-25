module

public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColDatK
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.HfArith
import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdOKP
import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdLat

public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.Ker
open Formalism.L2.Ker.Cd Formalism.L2.Th1.H
open Formalism.L2.Ker.Cd.IntegralLatticeDensity
open scoped BigOperators ComplexConjugate

namespace Supplements.Lattices.FourfoldCarrierProofs

/- The proof aliases infer their types from private providers so that importing this module
does not move generated equation declarations out of the caller. -/
set_option linter.defProp false

def up := @SO.up
def down := @SO.down
def selfDual := @SO.selfDual
def betaSemi := @SO.betaSemi
def exists_nat_clearing_order_denominators := @SO.exists_nat_clearing_order_denominators
def selfDual_image := @SO.selfDual_img
def exists_nat_mul := @SO.exists_nat_mul
def denom := @SO.denom
def lam_mul := @SO.lam_mul
def theta_eq := @SO.theta_eq
def lam_theta := @SO.lam_theta
def lamMM_smul := @SO.lamMM_smul
def int_mem_inverse_half_different := @SO.int_mem_inverse_half_different
def mem_iff := @SO.mem_iff
def theta_val := @SO.theta_val
def hθ := @SO.hθ
def hθ' := @SO.hθ'
def idx₁ := @SO.idx₁
def idx₂ := @SO.idx₂
def Lat0 := @Cd.Lat0
def isomOK := @Cd.Base.isomOK
def blockFourfold_hOne_eq_hOne := @Cd.blockFourfold_hOne_eq_hOne
def area_eq := @Cd.area_eq
def areaOK := @Cd.Base.areaOK
def omega_mem := @Cd.Base.omega_mem
def homL_std_entry := @Cd.homL_std_entry
def YYl_std_entry := @Cd.YYl_std_entry
def single_mem_homL := @Cd.single_mem_homL
def mem_stdL := @Cd.Inhab.mem_stdL
def single_mem_stdL := @Cd.Inhab.single_mem_stdL
def star_mem_range := @Cd.Inhab.star_mem_range
def stdL_isSD := @Cd.Inhab.stdL_isSD

theorem fg_of_nsmul_le {ι : Type} (M M' : AddSubgroup (ι → ℂ)) [AddGroup.FG M']
    (N : ℕ) (hN : 0 < N) (h : ∀ x ∈ M, N • x ∈ M') : AddGroup.FG M :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.SO.fg_of_nsmul_le M M' N hN h

theorem fourth_power_le_closure_embeddings {D : Car} (Λ : AddSubgroup ℂ) :
    pow4 (lamMM D Λ) ≤ AddSubgroup.closure
      {z | ∃ w ∈ Λ, ∃ y : Fin 4 → D.host.E, (∀ a, y a ∈ D.host.AA0) ∧
        z = w • fun p : Fin 4 × D.what₂.Tau => Cd.TaylorLogMetric.embT D p.2 (y p.1)} :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.SO.fourth_power_le_closure_embeddings Λ

theorem span_range_emb4_eq_top (D : Car) :
    Submodule.span ℂ (Set.range (fun (x : Fin 4 → D.host.E) (w : Fin 4 × D.what₂.Tau) =>
      Cd.TaylorLogMetric.embT D w.2 (x w.1))) = ⊤ :=
  Formalism.L2.Ker.Cd.span_range_emb4_eq_top D

theorem isoK_hermitian_sum_eq_emb4_hermitian_sum {D : Car}
    (γ : IsoK D) (x y : Fin 4 → D.host.E) :
    ∑ w, D.host.φ₀ ((γ.g x w : D.host.K) : D.host.E) * conj (D.host.φ₀ ((γ.g y w : D.host.K) : D.host.E))
      = ∑ w : Fin 4 × D.what₂.Tau, Cd.TaylorLogMetric.embT D w.2 (x w.1) *
          conj (Cd.TaylorLogMetric.embT D w.2 (y w.1)) :=
  Formalism.L2.Ker.Cd.isoK_hermitian_sum_eq_emb4_hermitian_sum γ x y

end Supplements.Lattices.FourfoldCarrierProofs
