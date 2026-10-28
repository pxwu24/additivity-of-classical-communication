import SchurEntropy.Capacity.StandardCriterion
import SchurEntropy.Capacity.OutputCenterCriterion

/-!
# Entropic criteria for additivity

`standard_entropic_criterion` proves the criterion preserving both marginal
states. `output_center_entropic_criterion` proves the weaker criterion
preserving only one output-center logarithmic expectation. Both use actual
finite-dimensional CPTP channels and Holevo information in bits.
-/
