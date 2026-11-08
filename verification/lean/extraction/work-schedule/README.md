# Reconstruction pricing and stage charge

Pinned Charon and Aeneas extract the original work schedule and charge wrapper
at the two selectors recorded in `receipt.json`. The complete schedule match
is projected together with its arithmetic helpers and the source charge tag.
The selected bodies and types agree with the filtered reconstruction extraction.
The projector also checks the shared meter and backend declarations before
reusing them from the existing bridge modules.

`WorkSchedule.number_refines` proves lossless conversion from either supported
pointer width. `WorkSchedule.mul_refines` proves the exact checked product for
every pair of u64 inputs, including the original work-limit error on overflow.
`WorkSchedule.reconstruct_refines` applies those results to the Reconstruct
tag, whose price is three times the capacity.

`StageCharge.charge_refines` preserves the pricing computation's control
outcomes and checks the exact source meter transition for each normal price.
A pricing error preserves the incoming meter. A successful price calls the
verified meter, including its checked addition, limit check and sticky
exhaustion. `StageCharge.reconstruct_refines` composes the wrapper with the
proved Reconstruct price.

Two concrete standard-library bindings supply the checked unsigned conversion
and the checked u64 shift used by the original schedule. The shift checks its
amount and retains the fixed-width bit result. Standard-library and extraction
correspondence remain part of the bridge trust boundary.

Run the projector from `verification/lean` with
`python3 extraction/work-schedule/project.py`. Build the proof from `bridge`
with `lake build BulksketchBridge.StageCharge` under the pinned Lean toolchain.
The frozen challenge names and checked source spans are recorded in
`refinement-receipt.json`.
