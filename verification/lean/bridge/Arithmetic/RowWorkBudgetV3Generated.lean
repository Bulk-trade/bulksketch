-- Original checked V3 row wrapper carrying the V2 sum-cost parameter.
import Arithmetic.RowWorkBudgetV2Generated
import Arithmetic.MaxAffineDegreeGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
noncomputable section
namespace bulksketch

/-- [bulksketch::decode::work::{bulksketch::decode::work::WorkScheduleV3}::row_bound]:
    Source: 'src/decode/work.rs', lines 332:4-384:5 -/
def decode.work.WorkScheduleV3.row_bound
  (sumCosts : RowWorkBudgetRuntime.SumCosts) (capacity : Std.Usize) (budget : Std.Usize) (beta : Std.Usize)
  (candidates : Std.Usize) :
  Result (core.result.Result types.WorkUnits types.DecodeError)
  := do
  let r ←
    decode.work.WorkScheduleV2.row_bound sumCosts capacity budget beta candidates
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ←
      decode.work.WorkScheduleV1.cost (decode.work.Charge.Verify capacity beta)
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r2 ←
        decode.work.WorkScheduleV1.cost (decode.work.Charge.VerifyLfsr capacity
          beta budget)
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let i ← lift (core.cmp.impls.OrdU64.max val2 val1)
        let i1 ← i - val1
        let r3 ← decode.work.add val i1
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let i2 ← decode.affine.MAX_PREFERRED_DEGREE
          let d ← lift (core.cmp.impls.OrdUsize.min budget i2)
          if d >= 3#usize
          then
            let r4 ←
              decode.work.WorkScheduleV1.cost
                (decode.work.Charge.AffinePreparation d)
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              let i3 ← d - 1#usize
              let r5 ←
                decode.work.WorkScheduleV1.cost
                  (decode.work.Charge.AffineEnumeration d i3)
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val5 =>
                let r6 ←
                  decode.work.WorkScheduleV1.cost
                    (decode.work.Charge.AffineSplit d i3)
                let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                match cf6 with
                | core.ops.control_flow.ControlFlow.Continue val6 =>
                  let r7 ← decode.work.number d
                  let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                  match cf7 with
                  | core.ops.control_flow.ControlFlow.Continue val7 =>
                    let i4 ← d - 2#usize
                    let r8 ← decode.work.number i4
                    let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
                    match cf8 with
                    | core.ops.control_flow.ControlFlow.Continue val8 =>
                      let r9 ← decode.work.mul val7 val8
                      let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r9
                      match cf9 with
                      | core.ops.control_flow.ControlFlow.Continue val9 =>
                        let r10 ← decode.work.mul val9 val6
                        let cf10 ←
                          core.result.Result.Insts.CoreOpsTry.branch r10
                        match cf10 with
                        | core.ops.control_flow.ControlFlow.Continue val10 =>
                          let i5 ←
                            lift (core.cmp.impls.OrdU64.max val5 val10)
                          let r11 ← decode.work.add val4 i5
                          let cf11 ←
                            core.result.Result.Insts.CoreOpsTry.branch r11
                          match cf11 with
                          | core.ops.control_flow.ControlFlow.Continue val11 =>
                            let r12 ← decode.work.add val3 val11
                            let cf12 ←
                              core.result.Result.Insts.CoreOpsTry.branch r12
                            match cf12 with
                            | core.ops.control_flow.ControlFlow.Continue val12
                              =>
                              if capacity >= 3#usize
                              then
                                if budget >= 3#usize
                                then
                                  let r13 ← decode.work.add 863#u64 val1
                                  let cf13 ←
                                    core.result.Result.Insts.CoreOpsTry.branch
                                      r13
                                  match cf13 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    val13 =>
                                    let r14 ← decode.work.add val12 val13
                                    let cf14 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r14
                                    match cf14 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val14 =>
                                      if capacity >= 4#usize
                                      then
                                        if budget >= 4#usize
                                        then
                                          let r15 ←
                                            decode.work.add 2337#u64 val1
                                          let cf15 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r15
                                          match cf15 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val15 =>
                                            let r16 ←
                                              decode.work.add val14 val15
                                            let cf16 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r16
                                            match cf16 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val16 =>
                                              let i6 ← budget / 3#usize
                                              let r17 ← decode.work.number i6
                                              let cf17 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  r17
                                              match cf17 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                val17 =>
                                                let r18 ←
                                                  decode.work.mul 671#u64 val17
                                                let cf18 ←
                                                  core.result.Result.Insts.CoreOpsTry.branch
                                                    r18
                                                match cf18 with
                                                |
                                                  core.ops.control_flow.ControlFlow.Continue
                                                  val18 =>
                                                  let i7 ← budget / 4#usize
                                                  let r19 ←
                                                    decode.work.number i7
                                                  let cf19 ←
                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                      r19
                                                  match cf19 with
                                                  |
                                                    core.ops.control_flow.ControlFlow.Continue
                                                    val19 =>
                                                    let r20 ←
                                                      decode.work.mul 2097#u64
                                                        val19
                                                    let cf20 ←
                                                      core.result.Result.Insts.CoreOpsTry.branch
                                                        r20
                                                    match cf20 with
                                                    |
                                                      core.ops.control_flow.ControlFlow.Continue
                                                      val20 =>
                                                      let r21 ←
                                                        decode.work.add val18
                                                          val20
                                                      let cf21 ←
                                                        core.result.Result.Insts.CoreOpsTry.branch
                                                          r21
                                                      match cf21 with
                                                      |
                                                        core.ops.control_flow.ControlFlow.Continue
                                                        val21 =>
                                                        let r22 ←
                                                          decode.work.add val16
                                                            val21
                                                        let cf22 ←
                                                          core.result.Result.Insts.CoreOpsTry.branch
                                                            r22
                                                        match cf22 with
                                                        |
                                                          core.ops.control_flow.ControlFlow.Continue
                                                          val22 =>
                                                          ok
                                                            (core.result.Result.Ok
                                                            val22)
                                                        |
                                                          core.ops.control_flow.ControlFlow.Break
                                                          residual =>
                                                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                            types.WorkUnits
                                                            (core.convert.FromSame
                                                            types.DecodeError)
                                                            residual
                                                      |
                                                        core.ops.control_flow.ControlFlow.Break
                                                        residual =>
                                                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                          types.WorkUnits
                                                          (core.convert.FromSame
                                                          types.DecodeError)
                                                          residual
                                                    |
                                                      core.ops.control_flow.ControlFlow.Break
                                                      residual =>
                                                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                        types.WorkUnits
                                                        (core.convert.FromSame
                                                        types.DecodeError)
                                                        residual
                                                  |
                                                    core.ops.control_flow.ControlFlow.Break
                                                    residual =>
                                                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                      types.WorkUnits
                                                      (core.convert.FromSame
                                                      types.DecodeError)
                                                      residual
                                                |
                                                  core.ops.control_flow.ControlFlow.Break
                                                  residual =>
                                                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                    types.WorkUnits
                                                    (core.convert.FromSame
                                                    types.DecodeError) residual
                                              |
                                                core.ops.control_flow.ControlFlow.Break
                                                residual =>
                                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                  types.WorkUnits
                                                  (core.convert.FromSame
                                                  types.DecodeError) residual
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                types.WorkUnits
                                                (core.convert.FromSame
                                                types.DecodeError) residual
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                              types.WorkUnits
                                              (core.convert.FromSame
                                              types.DecodeError) residual
                                        else
                                          let i6 ← budget / 3#usize
                                          let r15 ← decode.work.number i6
                                          let cf15 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r15
                                          match cf15 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val15 =>
                                            let r16 ←
                                              decode.work.mul 671#u64 val15
                                            let cf16 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r16
                                            match cf16 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val16 =>
                                              let i7 ← budget / 4#usize
                                              let r17 ← decode.work.number i7
                                              let cf17 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  r17
                                              match cf17 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                val17 =>
                                                let r18 ←
                                                  decode.work.mul 2097#u64
                                                    val17
                                                let cf18 ←
                                                  core.result.Result.Insts.CoreOpsTry.branch
                                                    r18
                                                match cf18 with
                                                |
                                                  core.ops.control_flow.ControlFlow.Continue
                                                  val18 =>
                                                  let r19 ←
                                                    decode.work.add val16 val18
                                                  let cf19 ←
                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                      r19
                                                  match cf19 with
                                                  |
                                                    core.ops.control_flow.ControlFlow.Continue
                                                    val19 =>
                                                    let r20 ←
                                                      decode.work.add val14
                                                        val19
                                                    let cf20 ←
                                                      core.result.Result.Insts.CoreOpsTry.branch
                                                        r20
                                                    match cf20 with
                                                    |
                                                      core.ops.control_flow.ControlFlow.Continue
                                                      val20 =>
                                                      ok (core.result.Result.Ok
                                                        val20)
                                                    |
                                                      core.ops.control_flow.ControlFlow.Break
                                                      residual =>
                                                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                        types.WorkUnits
                                                        (core.convert.FromSame
                                                        types.DecodeError)
                                                        residual
                                                  |
                                                    core.ops.control_flow.ControlFlow.Break
                                                    residual =>
                                                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                      types.WorkUnits
                                                      (core.convert.FromSame
                                                      types.DecodeError)
                                                      residual
                                                |
                                                  core.ops.control_flow.ControlFlow.Break
                                                  residual =>
                                                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                    types.WorkUnits
                                                    (core.convert.FromSame
                                                    types.DecodeError) residual
                                              |
                                                core.ops.control_flow.ControlFlow.Break
                                                residual =>
                                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                  types.WorkUnits
                                                  (core.convert.FromSame
                                                  types.DecodeError) residual
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                types.WorkUnits
                                                (core.convert.FromSame
                                                types.DecodeError) residual
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                              types.WorkUnits
                                              (core.convert.FromSame
                                              types.DecodeError) residual
                                      else
                                        let i6 ← budget / 3#usize
                                        let r15 ← decode.work.number i6
                                        let cf15 ←
                                          core.result.Result.Insts.CoreOpsTry.branch
                                            r15
                                        match cf15 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          val15 =>
                                          let r16 ←
                                            decode.work.mul 671#u64 val15
                                          let cf16 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r16
                                          match cf16 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val16 =>
                                            let i7 ← budget / 4#usize
                                            let r17 ← decode.work.number i7
                                            let cf17 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r17
                                            match cf17 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val17 =>
                                              let r18 ←
                                                decode.work.mul 2097#u64 val17
                                              let cf18 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  r18
                                              match cf18 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                val18 =>
                                                let r19 ←
                                                  decode.work.add val16 val18
                                                let cf19 ←
                                                  core.result.Result.Insts.CoreOpsTry.branch
                                                    r19
                                                match cf19 with
                                                |
                                                  core.ops.control_flow.ControlFlow.Continue
                                                  val19 =>
                                                  let r20 ←
                                                    decode.work.add val14 val19
                                                  let cf20 ←
                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                      r20
                                                  match cf20 with
                                                  |
                                                    core.ops.control_flow.ControlFlow.Continue
                                                    val20 =>
                                                    ok (core.result.Result.Ok
                                                      val20)
                                                  |
                                                    core.ops.control_flow.ControlFlow.Break
                                                    residual =>
                                                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                      types.WorkUnits
                                                      (core.convert.FromSame
                                                      types.DecodeError)
                                                      residual
                                                |
                                                  core.ops.control_flow.ControlFlow.Break
                                                  residual =>
                                                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                    types.WorkUnits
                                                    (core.convert.FromSame
                                                    types.DecodeError) residual
                                              |
                                                core.ops.control_flow.ControlFlow.Break
                                                residual =>
                                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                  types.WorkUnits
                                                  (core.convert.FromSame
                                                  types.DecodeError) residual
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                types.WorkUnits
                                                (core.convert.FromSame
                                                types.DecodeError) residual
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                              types.WorkUnits
                                              (core.convert.FromSame
                                              types.DecodeError) residual
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                            types.WorkUnits
                                            (core.convert.FromSame
                                            types.DecodeError) residual
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                        types.WorkUnits (core.convert.FromSame
                                        types.DecodeError) residual
                                  | core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                      types.WorkUnits (core.convert.FromSame
                                      types.DecodeError) residual
                                else
                                  if capacity >= 4#usize
                                  then
                                    if budget >= 4#usize
                                    then
                                      let r13 ← decode.work.add 2337#u64 val1
                                      let cf13 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r13
                                      match cf13 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val13 =>
                                        let r14 ← decode.work.add val12 val13
                                        let cf14 ←
                                          core.result.Result.Insts.CoreOpsTry.branch
                                            r14
                                        match cf14 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          val14 =>
                                          let i6 ← budget / 3#usize
                                          let r15 ← decode.work.number i6
                                          let cf15 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r15
                                          match cf15 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val15 =>
                                            let r16 ←
                                              decode.work.mul 671#u64 val15
                                            let cf16 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r16
                                            match cf16 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val16 =>
                                              let i7 ← budget / 4#usize
                                              let r17 ← decode.work.number i7
                                              let cf17 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  r17
                                              match cf17 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                val17 =>
                                                let r18 ←
                                                  decode.work.mul 2097#u64
                                                    val17
                                                let cf18 ←
                                                  core.result.Result.Insts.CoreOpsTry.branch
                                                    r18
                                                match cf18 with
                                                |
                                                  core.ops.control_flow.ControlFlow.Continue
                                                  val18 =>
                                                  let r19 ←
                                                    decode.work.add val16 val18
                                                  let cf19 ←
                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                      r19
                                                  match cf19 with
                                                  |
                                                    core.ops.control_flow.ControlFlow.Continue
                                                    val19 =>
                                                    let r20 ←
                                                      decode.work.add val14
                                                        val19
                                                    let cf20 ←
                                                      core.result.Result.Insts.CoreOpsTry.branch
                                                        r20
                                                    match cf20 with
                                                    |
                                                      core.ops.control_flow.ControlFlow.Continue
                                                      val20 =>
                                                      ok (core.result.Result.Ok
                                                        val20)
                                                    |
                                                      core.ops.control_flow.ControlFlow.Break
                                                      residual =>
                                                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                        types.WorkUnits
                                                        (core.convert.FromSame
                                                        types.DecodeError)
                                                        residual
                                                  |
                                                    core.ops.control_flow.ControlFlow.Break
                                                    residual =>
                                                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                      types.WorkUnits
                                                      (core.convert.FromSame
                                                      types.DecodeError)
                                                      residual
                                                |
                                                  core.ops.control_flow.ControlFlow.Break
                                                  residual =>
                                                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                    types.WorkUnits
                                                    (core.convert.FromSame
                                                    types.DecodeError) residual
                                              |
                                                core.ops.control_flow.ControlFlow.Break
                                                residual =>
                                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                  types.WorkUnits
                                                  (core.convert.FromSame
                                                  types.DecodeError) residual
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                types.WorkUnits
                                                (core.convert.FromSame
                                                types.DecodeError) residual
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                              types.WorkUnits
                                              (core.convert.FromSame
                                              types.DecodeError) residual
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                            types.WorkUnits
                                            (core.convert.FromSame
                                            types.DecodeError) residual
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                          types.WorkUnits
                                          (core.convert.FromSame
                                          types.DecodeError) residual
                                    else
                                      let i6 ← budget / 3#usize
                                      let r13 ← decode.work.number i6
                                      let cf13 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r13
                                      match cf13 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val13 =>
                                        let r14 ←
                                          decode.work.mul 671#u64 val13
                                        let cf14 ←
                                          core.result.Result.Insts.CoreOpsTry.branch
                                            r14
                                        match cf14 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          val14 =>
                                          let i7 ← budget / 4#usize
                                          let r15 ← decode.work.number i7
                                          let cf15 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r15
                                          match cf15 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val15 =>
                                            let r16 ←
                                              decode.work.mul 2097#u64 val15
                                            let cf16 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r16
                                            match cf16 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val16 =>
                                              let r17 ←
                                                decode.work.add val14 val16
                                              let cf17 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  r17
                                              match cf17 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                val17 =>
                                                let r18 ←
                                                  decode.work.add val12 val17
                                                let cf18 ←
                                                  core.result.Result.Insts.CoreOpsTry.branch
                                                    r18
                                                match cf18 with
                                                |
                                                  core.ops.control_flow.ControlFlow.Continue
                                                  val18 =>
                                                  ok (core.result.Result.Ok
                                                    val18)
                                                |
                                                  core.ops.control_flow.ControlFlow.Break
                                                  residual =>
                                                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                    types.WorkUnits
                                                    (core.convert.FromSame
                                                    types.DecodeError) residual
                                              |
                                                core.ops.control_flow.ControlFlow.Break
                                                residual =>
                                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                  types.WorkUnits
                                                  (core.convert.FromSame
                                                  types.DecodeError) residual
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                types.WorkUnits
                                                (core.convert.FromSame
                                                types.DecodeError) residual
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                              types.WorkUnits
                                              (core.convert.FromSame
                                              types.DecodeError) residual
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                            types.WorkUnits
                                            (core.convert.FromSame
                                            types.DecodeError) residual
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                          types.WorkUnits
                                          (core.convert.FromSame
                                          types.DecodeError) residual
                                  else
                                    let i6 ← budget / 3#usize
                                    let r13 ← decode.work.number i6
                                    let cf13 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r13
                                    match cf13 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val13 =>
                                      let r14 ← decode.work.mul 671#u64 val13
                                      let cf14 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r14
                                      match cf14 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val14 =>
                                        let i7 ← budget / 4#usize
                                        let r15 ← decode.work.number i7
                                        let cf15 ←
                                          core.result.Result.Insts.CoreOpsTry.branch
                                            r15
                                        match cf15 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          val15 =>
                                          let r16 ←
                                            decode.work.mul 2097#u64 val15
                                          let cf16 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r16
                                          match cf16 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val16 =>
                                            let r17 ←
                                              decode.work.add val14 val16
                                            let cf17 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r17
                                            match cf17 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val17 =>
                                              let r18 ←
                                                decode.work.add val12 val17
                                              let cf18 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  r18
                                              match cf18 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                val18 =>
                                                ok (core.result.Result.Ok
                                                  val18)
                                              |
                                                core.ops.control_flow.ControlFlow.Break
                                                residual =>
                                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                  types.WorkUnits
                                                  (core.convert.FromSame
                                                  types.DecodeError) residual
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                types.WorkUnits
                                                (core.convert.FromSame
                                                types.DecodeError) residual
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                              types.WorkUnits
                                              (core.convert.FromSame
                                              types.DecodeError) residual
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                            types.WorkUnits
                                            (core.convert.FromSame
                                            types.DecodeError) residual
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                          types.WorkUnits
                                          (core.convert.FromSame
                                          types.DecodeError) residual
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                        types.WorkUnits (core.convert.FromSame
                                        types.DecodeError) residual
                              else
                                if capacity >= 4#usize
                                then
                                  if budget >= 4#usize
                                  then
                                    let r13 ← decode.work.add 2337#u64 val1
                                    let cf13 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r13
                                    match cf13 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val13 =>
                                      let r14 ← decode.work.add val12 val13
                                      let cf14 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r14
                                      match cf14 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val14 =>
                                        let i6 ← budget / 3#usize
                                        let r15 ← decode.work.number i6
                                        let cf15 ←
                                          core.result.Result.Insts.CoreOpsTry.branch
                                            r15
                                        match cf15 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          val15 =>
                                          let r16 ←
                                            decode.work.mul 671#u64 val15
                                          let cf16 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r16
                                          match cf16 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val16 =>
                                            let i7 ← budget / 4#usize
                                            let r17 ← decode.work.number i7
                                            let cf17 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r17
                                            match cf17 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val17 =>
                                              let r18 ←
                                                decode.work.mul 2097#u64 val17
                                              let cf18 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  r18
                                              match cf18 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                val18 =>
                                                let r19 ←
                                                  decode.work.add val16 val18
                                                let cf19 ←
                                                  core.result.Result.Insts.CoreOpsTry.branch
                                                    r19
                                                match cf19 with
                                                |
                                                  core.ops.control_flow.ControlFlow.Continue
                                                  val19 =>
                                                  let r20 ←
                                                    decode.work.add val14 val19
                                                  let cf20 ←
                                                    core.result.Result.Insts.CoreOpsTry.branch
                                                      r20
                                                  match cf20 with
                                                  |
                                                    core.ops.control_flow.ControlFlow.Continue
                                                    val20 =>
                                                    ok (core.result.Result.Ok
                                                      val20)
                                                  |
                                                    core.ops.control_flow.ControlFlow.Break
                                                    residual =>
                                                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                      types.WorkUnits
                                                      (core.convert.FromSame
                                                      types.DecodeError)
                                                      residual
                                                |
                                                  core.ops.control_flow.ControlFlow.Break
                                                  residual =>
                                                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                    types.WorkUnits
                                                    (core.convert.FromSame
                                                    types.DecodeError) residual
                                              |
                                                core.ops.control_flow.ControlFlow.Break
                                                residual =>
                                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                  types.WorkUnits
                                                  (core.convert.FromSame
                                                  types.DecodeError) residual
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                types.WorkUnits
                                                (core.convert.FromSame
                                                types.DecodeError) residual
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                              types.WorkUnits
                                              (core.convert.FromSame
                                              types.DecodeError) residual
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                            types.WorkUnits
                                            (core.convert.FromSame
                                            types.DecodeError) residual
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                          types.WorkUnits
                                          (core.convert.FromSame
                                          types.DecodeError) residual
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                        types.WorkUnits (core.convert.FromSame
                                        types.DecodeError) residual
                                  else
                                    let i6 ← budget / 3#usize
                                    let r13 ← decode.work.number i6
                                    let cf13 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r13
                                    match cf13 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val13 =>
                                      let r14 ← decode.work.mul 671#u64 val13
                                      let cf14 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r14
                                      match cf14 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val14 =>
                                        let i7 ← budget / 4#usize
                                        let r15 ← decode.work.number i7
                                        let cf15 ←
                                          core.result.Result.Insts.CoreOpsTry.branch
                                            r15
                                        match cf15 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          val15 =>
                                          let r16 ←
                                            decode.work.mul 2097#u64 val15
                                          let cf16 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r16
                                          match cf16 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val16 =>
                                            let r17 ←
                                              decode.work.add val14 val16
                                            let cf17 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r17
                                            match cf17 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val17 =>
                                              let r18 ←
                                                decode.work.add val12 val17
                                              let cf18 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  r18
                                              match cf18 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                val18 =>
                                                ok (core.result.Result.Ok
                                                  val18)
                                              |
                                                core.ops.control_flow.ControlFlow.Break
                                                residual =>
                                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                  types.WorkUnits
                                                  (core.convert.FromSame
                                                  types.DecodeError) residual
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                types.WorkUnits
                                                (core.convert.FromSame
                                                types.DecodeError) residual
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                              types.WorkUnits
                                              (core.convert.FromSame
                                              types.DecodeError) residual
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                            types.WorkUnits
                                            (core.convert.FromSame
                                            types.DecodeError) residual
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                          types.WorkUnits
                                          (core.convert.FromSame
                                          types.DecodeError) residual
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                        types.WorkUnits (core.convert.FromSame
                                        types.DecodeError) residual
                                else
                                  let i6 ← budget / 3#usize
                                  let r13 ← decode.work.number i6
                                  let cf13 ←
                                    core.result.Result.Insts.CoreOpsTry.branch
                                      r13
                                  match cf13 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    val13 =>
                                    let r14 ← decode.work.mul 671#u64 val13
                                    let cf14 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r14
                                    match cf14 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val14 =>
                                      let i7 ← budget / 4#usize
                                      let r15 ← decode.work.number i7
                                      let cf15 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r15
                                      match cf15 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val15 =>
                                        let r16 ←
                                          decode.work.mul 2097#u64 val15
                                        let cf16 ←
                                          core.result.Result.Insts.CoreOpsTry.branch
                                            r16
                                        match cf16 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          val16 =>
                                          let r17 ←
                                            decode.work.add val14 val16
                                          let cf17 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r17
                                          match cf17 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val17 =>
                                            let r18 ←
                                              decode.work.add val12 val17
                                            let cf18 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r18
                                            match cf18 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val18 =>
                                              ok (core.result.Result.Ok val18)
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                                types.WorkUnits
                                                (core.convert.FromSame
                                                types.DecodeError) residual
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                              types.WorkUnits
                                              (core.convert.FromSame
                                              types.DecodeError) residual
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                            types.WorkUnits
                                            (core.convert.FromSame
                                            types.DecodeError) residual
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                          types.WorkUnits
                                          (core.convert.FromSame
                                          types.DecodeError) residual
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                        types.WorkUnits (core.convert.FromSame
                                        types.DecodeError) residual
                                  | core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                      types.WorkUnits (core.convert.FromSame
                                      types.DecodeError) residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                types.WorkUnits (core.convert.FromSame
                                types.DecodeError) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                              types.WorkUnits (core.convert.FromSame
                              types.DecodeError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                            types.WorkUnits (core.convert.FromSame
                            types.DecodeError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          types.WorkUnits (core.convert.FromSame
                          types.DecodeError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        types.WorkUnits (core.convert.FromSame
                        types.DecodeError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      types.WorkUnits (core.convert.FromSame types.DecodeError)
                      residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    types.WorkUnits (core.convert.FromSame types.DecodeError)
                    residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  types.WorkUnits (core.convert.FromSame types.DecodeError)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                types.WorkUnits (core.convert.FromSame types.DecodeError)
                residual
          else
            if capacity >= 3#usize
            then
              if budget >= 3#usize
              then
                let r4 ← decode.work.add 863#u64 val1
                let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue val4 =>
                  let r5 ← decode.work.add val3 val4
                  let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue val5 =>
                    if capacity >= 4#usize
                    then
                      if budget >= 4#usize
                      then
                        let r6 ← decode.work.add 2337#u64 val1
                        let cf6 ←
                          core.result.Result.Insts.CoreOpsTry.branch r6
                        match cf6 with
                        | core.ops.control_flow.ControlFlow.Continue val6 =>
                          let r7 ← decode.work.add val5 val6
                          let cf7 ←
                            core.result.Result.Insts.CoreOpsTry.branch r7
                          match cf7 with
                          | core.ops.control_flow.ControlFlow.Continue val7 =>
                            let i3 ← budget / 3#usize
                            let r8 ← decode.work.number i3
                            let cf8 ←
                              core.result.Result.Insts.CoreOpsTry.branch r8
                            match cf8 with
                            | core.ops.control_flow.ControlFlow.Continue val8
                              =>
                              let r9 ← decode.work.mul 671#u64 val8
                              let cf9 ←
                                core.result.Result.Insts.CoreOpsTry.branch r9
                              match cf9 with
                              | core.ops.control_flow.ControlFlow.Continue val9
                                =>
                                let i4 ← budget / 4#usize
                                let r10 ← decode.work.number i4
                                let cf10 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r10
                                match cf10 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val10 =>
                                  let r11 ← decode.work.mul 2097#u64 val10
                                  let cf11 ←
                                    core.result.Result.Insts.CoreOpsTry.branch
                                      r11
                                  match cf11 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    val11 =>
                                    let r12 ← decode.work.add val9 val11
                                    let cf12 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r12
                                    match cf12 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val12 =>
                                      let r13 ← decode.work.add val7 val12
                                      let cf13 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r13
                                      match cf13 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val13 =>
                                        ok (core.result.Result.Ok val13)
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                          types.WorkUnits
                                          (core.convert.FromSame
                                          types.DecodeError) residual
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                        types.WorkUnits (core.convert.FromSame
                                        types.DecodeError) residual
                                  | core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                      types.WorkUnits (core.convert.FromSame
                                      types.DecodeError) residual
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                    types.WorkUnits (core.convert.FromSame
                                    types.DecodeError) residual
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                  types.WorkUnits (core.convert.FromSame
                                  types.DecodeError) residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                types.WorkUnits (core.convert.FromSame
                                types.DecodeError) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                              types.WorkUnits (core.convert.FromSame
                              types.DecodeError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                            types.WorkUnits (core.convert.FromSame
                            types.DecodeError) residual
                      else
                        let i3 ← budget / 3#usize
                        let r6 ← decode.work.number i3
                        let cf6 ←
                          core.result.Result.Insts.CoreOpsTry.branch r6
                        match cf6 with
                        | core.ops.control_flow.ControlFlow.Continue val6 =>
                          let r7 ← decode.work.mul 671#u64 val6
                          let cf7 ←
                            core.result.Result.Insts.CoreOpsTry.branch r7
                          match cf7 with
                          | core.ops.control_flow.ControlFlow.Continue val7 =>
                            let i4 ← budget / 4#usize
                            let r8 ← decode.work.number i4
                            let cf8 ←
                              core.result.Result.Insts.CoreOpsTry.branch r8
                            match cf8 with
                            | core.ops.control_flow.ControlFlow.Continue val8
                              =>
                              let r9 ← decode.work.mul 2097#u64 val8
                              let cf9 ←
                                core.result.Result.Insts.CoreOpsTry.branch r9
                              match cf9 with
                              | core.ops.control_flow.ControlFlow.Continue val9
                                =>
                                let r10 ← decode.work.add val7 val9
                                let cf10 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r10
                                match cf10 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val10 =>
                                  let r11 ← decode.work.add val5 val10
                                  let cf11 ←
                                    core.result.Result.Insts.CoreOpsTry.branch
                                      r11
                                  match cf11 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    val11 =>
                                    ok (core.result.Result.Ok val11)
                                  | core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                      types.WorkUnits (core.convert.FromSame
                                      types.DecodeError) residual
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                    types.WorkUnits (core.convert.FromSame
                                    types.DecodeError) residual
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                  types.WorkUnits (core.convert.FromSame
                                  types.DecodeError) residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                types.WorkUnits (core.convert.FromSame
                                types.DecodeError) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                              types.WorkUnits (core.convert.FromSame
                              types.DecodeError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                            types.WorkUnits (core.convert.FromSame
                            types.DecodeError) residual
                    else
                      let i3 ← budget / 3#usize
                      let r6 ← decode.work.number i3
                      let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                      match cf6 with
                      | core.ops.control_flow.ControlFlow.Continue val6 =>
                        let r7 ← decode.work.mul 671#u64 val6
                        let cf7 ←
                          core.result.Result.Insts.CoreOpsTry.branch r7
                        match cf7 with
                        | core.ops.control_flow.ControlFlow.Continue val7 =>
                          let i4 ← budget / 4#usize
                          let r8 ← decode.work.number i4
                          let cf8 ←
                            core.result.Result.Insts.CoreOpsTry.branch r8
                          match cf8 with
                          | core.ops.control_flow.ControlFlow.Continue val8 =>
                            let r9 ← decode.work.mul 2097#u64 val8
                            let cf9 ←
                              core.result.Result.Insts.CoreOpsTry.branch r9
                            match cf9 with
                            | core.ops.control_flow.ControlFlow.Continue val9
                              =>
                              let r10 ← decode.work.add val7 val9
                              let cf10 ←
                                core.result.Result.Insts.CoreOpsTry.branch r10
                              match cf10 with
                              | core.ops.control_flow.ControlFlow.Continue
                                val10 =>
                                let r11 ← decode.work.add val5 val10
                                let cf11 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r11
                                match cf11 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val11 =>
                                  ok (core.result.Result.Ok val11)
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                    types.WorkUnits (core.convert.FromSame
                                    types.DecodeError) residual
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                  types.WorkUnits (core.convert.FromSame
                                  types.DecodeError) residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                types.WorkUnits (core.convert.FromSame
                                types.DecodeError) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                              types.WorkUnits (core.convert.FromSame
                              types.DecodeError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                            types.WorkUnits (core.convert.FromSame
                            types.DecodeError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          types.WorkUnits (core.convert.FromSame
                          types.DecodeError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      types.WorkUnits (core.convert.FromSame types.DecodeError)
                      residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    types.WorkUnits (core.convert.FromSame types.DecodeError)
                    residual
              else
                if capacity >= 4#usize
                then
                  if budget >= 4#usize
                  then
                    let r4 ← decode.work.add 2337#u64 val1
                    let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
                    match cf4 with
                    | core.ops.control_flow.ControlFlow.Continue val4 =>
                      let r5 ← decode.work.add val3 val4
                      let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                      match cf5 with
                      | core.ops.control_flow.ControlFlow.Continue val5 =>
                        let i3 ← budget / 3#usize
                        let r6 ← decode.work.number i3
                        let cf6 ←
                          core.result.Result.Insts.CoreOpsTry.branch r6
                        match cf6 with
                        | core.ops.control_flow.ControlFlow.Continue val6 =>
                          let r7 ← decode.work.mul 671#u64 val6
                          let cf7 ←
                            core.result.Result.Insts.CoreOpsTry.branch r7
                          match cf7 with
                          | core.ops.control_flow.ControlFlow.Continue val7 =>
                            let i4 ← budget / 4#usize
                            let r8 ← decode.work.number i4
                            let cf8 ←
                              core.result.Result.Insts.CoreOpsTry.branch r8
                            match cf8 with
                            | core.ops.control_flow.ControlFlow.Continue val8
                              =>
                              let r9 ← decode.work.mul 2097#u64 val8
                              let cf9 ←
                                core.result.Result.Insts.CoreOpsTry.branch r9
                              match cf9 with
                              | core.ops.control_flow.ControlFlow.Continue val9
                                =>
                                let r10 ← decode.work.add val7 val9
                                let cf10 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r10
                                match cf10 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val10 =>
                                  let r11 ← decode.work.add val5 val10
                                  let cf11 ←
                                    core.result.Result.Insts.CoreOpsTry.branch
                                      r11
                                  match cf11 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    val11 =>
                                    ok (core.result.Result.Ok val11)
                                  | core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                      types.WorkUnits (core.convert.FromSame
                                      types.DecodeError) residual
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                    types.WorkUnits (core.convert.FromSame
                                    types.DecodeError) residual
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                  types.WorkUnits (core.convert.FromSame
                                  types.DecodeError) residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                types.WorkUnits (core.convert.FromSame
                                types.DecodeError) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                              types.WorkUnits (core.convert.FromSame
                              types.DecodeError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                            types.WorkUnits (core.convert.FromSame
                            types.DecodeError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          types.WorkUnits (core.convert.FromSame
                          types.DecodeError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        types.WorkUnits (core.convert.FromSame
                        types.DecodeError) residual
                  else
                    let i3 ← budget / 3#usize
                    let r4 ← decode.work.number i3
                    let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
                    match cf4 with
                    | core.ops.control_flow.ControlFlow.Continue val4 =>
                      let r5 ← decode.work.mul 671#u64 val4
                      let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                      match cf5 with
                      | core.ops.control_flow.ControlFlow.Continue val5 =>
                        let i4 ← budget / 4#usize
                        let r6 ← decode.work.number i4
                        let cf6 ←
                          core.result.Result.Insts.CoreOpsTry.branch r6
                        match cf6 with
                        | core.ops.control_flow.ControlFlow.Continue val6 =>
                          let r7 ← decode.work.mul 2097#u64 val6
                          let cf7 ←
                            core.result.Result.Insts.CoreOpsTry.branch r7
                          match cf7 with
                          | core.ops.control_flow.ControlFlow.Continue val7 =>
                            let r8 ← decode.work.add val5 val7
                            let cf8 ←
                              core.result.Result.Insts.CoreOpsTry.branch r8
                            match cf8 with
                            | core.ops.control_flow.ControlFlow.Continue val8
                              =>
                              let r9 ← decode.work.add val3 val8
                              let cf9 ←
                                core.result.Result.Insts.CoreOpsTry.branch r9
                              match cf9 with
                              | core.ops.control_flow.ControlFlow.Continue val9
                                =>
                                ok (core.result.Result.Ok val9)
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                  types.WorkUnits (core.convert.FromSame
                                  types.DecodeError) residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                types.WorkUnits (core.convert.FromSame
                                types.DecodeError) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                              types.WorkUnits (core.convert.FromSame
                              types.DecodeError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                            types.WorkUnits (core.convert.FromSame
                            types.DecodeError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          types.WorkUnits (core.convert.FromSame
                          types.DecodeError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        types.WorkUnits (core.convert.FromSame
                        types.DecodeError) residual
                else
                  let i3 ← budget / 3#usize
                  let r4 ← decode.work.number i3
                  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
                  match cf4 with
                  | core.ops.control_flow.ControlFlow.Continue val4 =>
                    let r5 ← decode.work.mul 671#u64 val4
                    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                    match cf5 with
                    | core.ops.control_flow.ControlFlow.Continue val5 =>
                      let i4 ← budget / 4#usize
                      let r6 ← decode.work.number i4
                      let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                      match cf6 with
                      | core.ops.control_flow.ControlFlow.Continue val6 =>
                        let r7 ← decode.work.mul 2097#u64 val6
                        let cf7 ←
                          core.result.Result.Insts.CoreOpsTry.branch r7
                        match cf7 with
                        | core.ops.control_flow.ControlFlow.Continue val7 =>
                          let r8 ← decode.work.add val5 val7
                          let cf8 ←
                            core.result.Result.Insts.CoreOpsTry.branch r8
                          match cf8 with
                          | core.ops.control_flow.ControlFlow.Continue val8 =>
                            let r9 ← decode.work.add val3 val8
                            let cf9 ←
                              core.result.Result.Insts.CoreOpsTry.branch r9
                            match cf9 with
                            | core.ops.control_flow.ControlFlow.Continue val9
                              =>
                              ok (core.result.Result.Ok val9)
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                types.WorkUnits (core.convert.FromSame
                                types.DecodeError) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                              types.WorkUnits (core.convert.FromSame
                              types.DecodeError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                            types.WorkUnits (core.convert.FromSame
                            types.DecodeError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          types.WorkUnits (core.convert.FromSame
                          types.DecodeError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        types.WorkUnits (core.convert.FromSame
                        types.DecodeError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      types.WorkUnits (core.convert.FromSame types.DecodeError)
                      residual
            else
              if capacity >= 4#usize
              then
                if budget >= 4#usize
                then
                  let r4 ← decode.work.add 2337#u64 val1
                  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
                  match cf4 with
                  | core.ops.control_flow.ControlFlow.Continue val4 =>
                    let r5 ← decode.work.add val3 val4
                    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                    match cf5 with
                    | core.ops.control_flow.ControlFlow.Continue val5 =>
                      let i3 ← budget / 3#usize
                      let r6 ← decode.work.number i3
                      let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                      match cf6 with
                      | core.ops.control_flow.ControlFlow.Continue val6 =>
                        let r7 ← decode.work.mul 671#u64 val6
                        let cf7 ←
                          core.result.Result.Insts.CoreOpsTry.branch r7
                        match cf7 with
                        | core.ops.control_flow.ControlFlow.Continue val7 =>
                          let i4 ← budget / 4#usize
                          let r8 ← decode.work.number i4
                          let cf8 ←
                            core.result.Result.Insts.CoreOpsTry.branch r8
                          match cf8 with
                          | core.ops.control_flow.ControlFlow.Continue val8 =>
                            let r9 ← decode.work.mul 2097#u64 val8
                            let cf9 ←
                              core.result.Result.Insts.CoreOpsTry.branch r9
                            match cf9 with
                            | core.ops.control_flow.ControlFlow.Continue val9
                              =>
                              let r10 ← decode.work.add val7 val9
                              let cf10 ←
                                core.result.Result.Insts.CoreOpsTry.branch r10
                              match cf10 with
                              | core.ops.control_flow.ControlFlow.Continue
                                val10 =>
                                let r11 ← decode.work.add val5 val10
                                let cf11 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r11
                                match cf11 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val11 =>
                                  ok (core.result.Result.Ok val11)
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                    types.WorkUnits (core.convert.FromSame
                                    types.DecodeError) residual
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                  types.WorkUnits (core.convert.FromSame
                                  types.DecodeError) residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                types.WorkUnits (core.convert.FromSame
                                types.DecodeError) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                              types.WorkUnits (core.convert.FromSame
                              types.DecodeError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                            types.WorkUnits (core.convert.FromSame
                            types.DecodeError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          types.WorkUnits (core.convert.FromSame
                          types.DecodeError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        types.WorkUnits (core.convert.FromSame
                        types.DecodeError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      types.WorkUnits (core.convert.FromSame types.DecodeError)
                      residual
                else
                  let i3 ← budget / 3#usize
                  let r4 ← decode.work.number i3
                  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
                  match cf4 with
                  | core.ops.control_flow.ControlFlow.Continue val4 =>
                    let r5 ← decode.work.mul 671#u64 val4
                    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                    match cf5 with
                    | core.ops.control_flow.ControlFlow.Continue val5 =>
                      let i4 ← budget / 4#usize
                      let r6 ← decode.work.number i4
                      let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                      match cf6 with
                      | core.ops.control_flow.ControlFlow.Continue val6 =>
                        let r7 ← decode.work.mul 2097#u64 val6
                        let cf7 ←
                          core.result.Result.Insts.CoreOpsTry.branch r7
                        match cf7 with
                        | core.ops.control_flow.ControlFlow.Continue val7 =>
                          let r8 ← decode.work.add val5 val7
                          let cf8 ←
                            core.result.Result.Insts.CoreOpsTry.branch r8
                          match cf8 with
                          | core.ops.control_flow.ControlFlow.Continue val8 =>
                            let r9 ← decode.work.add val3 val8
                            let cf9 ←
                              core.result.Result.Insts.CoreOpsTry.branch r9
                            match cf9 with
                            | core.ops.control_flow.ControlFlow.Continue val9
                              =>
                              ok (core.result.Result.Ok val9)
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                                types.WorkUnits (core.convert.FromSame
                                types.DecodeError) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                              types.WorkUnits (core.convert.FromSame
                              types.DecodeError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                            types.WorkUnits (core.convert.FromSame
                            types.DecodeError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          types.WorkUnits (core.convert.FromSame
                          types.DecodeError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        types.WorkUnits (core.convert.FromSame
                        types.DecodeError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      types.WorkUnits (core.convert.FromSame types.DecodeError)
                      residual
              else
                let i3 ← budget / 3#usize
                let r4 ← decode.work.number i3
                let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue val4 =>
                  let r5 ← decode.work.mul 671#u64 val4
                  let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue val5 =>
                    let i4 ← budget / 4#usize
                    let r6 ← decode.work.number i4
                    let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue val6 =>
                      let r7 ← decode.work.mul 2097#u64 val6
                      let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf7 with
                      | core.ops.control_flow.ControlFlow.Continue val7 =>
                        let r8 ← decode.work.add val5 val7
                        let cf8 ←
                          core.result.Result.Insts.CoreOpsTry.branch r8
                        match cf8 with
                        | core.ops.control_flow.ControlFlow.Continue val8 =>
                          let r9 ← decode.work.add val3 val8
                          let cf9 ←
                            core.result.Result.Insts.CoreOpsTry.branch r9
                          match cf9 with
                          | core.ops.control_flow.ControlFlow.Continue val9 =>
                            ok (core.result.Result.Ok val9)
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                              types.WorkUnits (core.convert.FromSame
                              types.DecodeError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                            types.WorkUnits (core.convert.FromSame
                            types.DecodeError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                          types.WorkUnits (core.convert.FromSame
                          types.DecodeError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        types.WorkUnits (core.convert.FromSame
                        types.DecodeError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      types.WorkUnits (core.convert.FromSame types.DecodeError)
                      residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    types.WorkUnits (core.convert.FromSame types.DecodeError)
                    residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            types.WorkUnits (core.convert.FromSame types.DecodeError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          types.WorkUnits (core.convert.FromSame types.DecodeError) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        types.WorkUnits (core.convert.FromSame types.DecodeError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      types.WorkUnits (core.convert.FromSame types.DecodeError) residual

end bulksketch
