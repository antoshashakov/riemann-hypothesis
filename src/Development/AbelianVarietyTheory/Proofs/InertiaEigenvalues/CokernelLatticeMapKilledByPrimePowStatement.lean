module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelLatticeMapKilledByPrimePow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.cokernel_latticeMap_killed_by_prime_pow : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Stmt := by
  first | exact @GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main | exact GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main | (intros; apply GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main <;> assumption)
