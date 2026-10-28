import SchurEntropy.Results
import SchurEntropy.EntropyScaling
import SchurEntropy.Capacity.Results

/-!
# Formal proofs accompanying the manuscript

The three matrix results are exported through `Results`:
`optimizedConcavity`, `scalar_joint_convexity`, and `block_entropy_inequality`.
The two entropic criteria are exported through `Capacity.Results`:
`Capacity.standard_entropic_criterion` and
`Capacity.output_center_entropic_criterion`.
The underlying statements use unnormalized spectral entropy in bits on actual
complex matrices, concrete CPTP maps, and finite state ensembles. No additional
analytic assumptions are introduced.
-/
