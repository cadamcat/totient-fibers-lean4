import Erdos821.Assembly
import Erdos821.Blueprint.Assembly
import Erdos821.P1.ClassicalInputs
import Erdos821.P8Grid.ProxyInputs
import Erdos821.P7.Geometry
import Erdos821.P7.FinalBounds
import Erdos821.P7Char.Combine
import Erdos821.S34.IdealInputs
import Erdos821.Prelim.SieveInputsProof
import Erdos821.S56.TypeIIProof
import Erdos821.Count.Count
import Erdos821.S9.FinalProof
import Erdos821.S10.Extraction
import Erdos821.P3Final.Transference
import Erdos821.P3Rare.Proof
import Erdos821.P5.ShiftTwoTasks
import Erdos821.P5MinorAdapter.Proof
import Erdos821.P5MarkedEnergy.Main

namespace Erdos821.Final

open Erdos821.Blueprint

/-! Exact type checks for every non-blueprint package theorem used below. -/
example : ClassicalInputs := Erdos821.Blueprint.classical_inputs

example : Erdos821.Blueprint.proxy_inputs_statement :=
  @Erdos821.Blueprint.proxy_inputs_proof

example : Erdos821.Blueprint.sieve_inputs_statement :=
  @Erdos821.Blueprint.sieve_inputs_proof

example : Erdos821.Blueprint.candidate_geometry_statement :=
  @Erdos821.Blueprint.candidate_geometry_proof

example : Erdos821.Blueprint.candidate_bounds_statement :=
  @Erdos821.Blueprint.candidate_bounds_proof

example : Erdos821.Blueprint.candidate_typeI_statement :=
  @Erdos821.P7Char.candidate_typeI_via_nonprincipal

example : Erdos821.Blueprint.typeII_estimate_statement :=
  @Erdos821.Blueprint.typeII_estimate_proof

example : type_of% @Erdos821.Blueprint.count_from_weighted_mass :=
  @Erdos821.Blueprint.count_from_weighted_mass

example : Erdos821.Blueprint.ideal_inputs_statement :=
  @Erdos821.Blueprint.ideal_inputs_proof

example : Erdos821.Blueprint.balanced_rough_bound_statement :=
  @Erdos821.Blueprint.balanced_rough_bound_proof

example : Erdos821.Blueprint.prime_extraction_statement :=
  @Erdos821.Blueprint.prime_extraction_proof

/-- The best currently proved assembly of the ten exact package interfaces. -/
theorem packageInterfaces : PackageInterfaces where
  classical := Erdos821.Blueprint.classical_inputs
  sieve := Erdos821.Blueprint.sieve_inputs_proof
  transference := Erdos821.P3Final.transference_inputs_of_rare
    Erdos821.S2Core.MemoryRareTask_proof
  ideal := Erdos821.Blueprint.ideal_inputs_proof
  shift := Erdos821.P5Core.shifted_cancellation_of_two_tasks
    Erdos821.P5Core.ComparisonMinorArcAdapterTask_proof
    Erdos821.P5Core.MarkedEndpointEnergyTask_proof
  typeII := Erdos821.Blueprint.typeII_estimate_proof
  proxies := Erdos821.Blueprint.proxy_inputs_proof
  candidateGeometry := fun δ hδ hδ' =>
    Erdos821.Blueprint.candidate_geometry_proof Erdos821.Blueprint.classical_inputs
      δ hδ hδ'
  candidateBounds := Erdos821.Blueprint.candidate_bounds_proof
    Erdos821.Blueprint.classical_inputs
  candidateTypeI := Erdos821.P7Char.candidate_typeI_via_nonprincipal
    Erdos821.Blueprint.classical_inputs
  balanced := Erdos821.Blueprint.balanced_rough_bound_proof
    Erdos821.Blueprint.classical_inputs
    (Erdos821.Blueprint.sieve_inputs_proof Erdos821.Blueprint.classical_inputs)
  extraction := Erdos821.Blueprint.prime_extraction_proof
  count := Erdos821.Blueprint.count_from_weighted_mass

theorem supply : Erdos821.SmoothShiftedPrimeSupply :=
  Erdos821.Blueprint.supply_of_package_interfaces packageInterfaces

/-- Erdős 821 assembled from the currently available package proofs. -/
theorem statement : Erdos821.Statement :=
  Erdos821.statement_of_supply supply

end Erdos821.Final
