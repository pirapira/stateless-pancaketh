import Guest.Basic

/-!
# The guest's own SSZ decoding of the stateless input, as a function of bytes

`Guest.StepBound.declaredBlockGasLimit` needs the block gas limit the input
declares, and needs it to be `none` exactly when the input does not decode.
This module mirrors the guest's decoder for that purpose: `decode_payload`,
`decode_requests`, `decode_bytes_list` and `decode_stateless_input` of
`guest/src/ssz.pnk`, with their helpers `ssz_check_offsets`,
`ssz_split_var_list`, `ssz_fixed_list_count` and `ssz_optional_u64`, and the
field offsets and list limits of `guest/src/types.h`. Every `ssz_fail` site
becomes `none`, in the guest's own order, so `decodeStatelessInput` is `some`
on exactly the inputs on which `decode_stateless_input` returns instead of
raising `SszErr`.

This is *platform* code: it fixes the premise of the step-bound theorem, so it
follows the guest and is not to be adjusted to suit a proof.

## What "as a function of bytes" means

`input_blob` (`guest/src/lib/mem.pnk`) copies the blob from the host input
region into the heap as `⌈len/8⌉` words, so the decoder reads the blob
followed by zeros: the input region is zero padded, and `Guest.guestInitialMemory`
zero-fills the heap. Hence `byteAt`. Every read the decoder makes lies within
`[0, len + 8)` — offsets are checked against `len` before use, and the widest
read past one is the four bytes of an `LD_LE32` — so the zeros are all it ever
sees beyond the blob.

Decoding is a property of the bytes alone; it says nothing about whether the
guest has the *memory* to decode them. `alloc` traps once the heap is
exhausted, and an input can be decodable and still far too large to copy into
the heap (see `Guest.StepBound`).
-/

namespace Guest.InputDecode

/-! ### Bytes and little-endian scalars, as `ld8`, `LD_LE32` and `LD_LE64` -/

/-- Byte at blob offset `i` as the guest reads it back from the heap: the blob,
then zeros. -/
def byteAt (input : InputBlob) (i : Nat) : Nat := ((input[i]?).getD 0).toNat

/-- `LD_LE32`. -/
def le32 (input : InputBlob) (i : Nat) : Nat :=
  byteAt input i + byteAt input (i + 1) * 256 + byteAt input (i + 2) * 65536 +
    byteAt input (i + 3) * 16777216

/-- `LD_LE64`. -/
def le64 (input : InputBlob) (i : Nat) : Nat :=
  le32 input i + le32 input (i + 4) * 4294967296

/-! ### Field offsets and list limits (`guest/src/types.h`) -/

/-- `SI_FIXED`. -/ def siFixed : Nat := 16
/-- `NPR_FIXED`. -/ def nprFixed : Nat := 44
/-- `PL_FIXED`. -/ def plFixed : Nat := 540
/-- `REQ_FIXED`. -/ def reqFixed : Nat := 20

/-- `PLO_EXTRA_OFF`. -/ def ploExtraOff : Nat := 436
/-- `PLO_TXS_OFF`. -/ def ploTxsOff : Nat := 504
/-- `PLO_WD_OFF`. -/ def ploWdOff : Nat := 508
/-- `PLO_BAL_OFF`. -/ def ploBalOff : Nat := 528
/-- `PLO_NUMBER`. -/ def ploNumber : Nat := 404
/-- `PLO_GAS_LIMIT`. -/ def ploGasLimit : Nat := 412
/-- `PLO_GAS_USED`. -/ def ploGasUsed : Nat := 420
/-- `PLO_TIMESTAMP`. -/ def ploTimestamp : Nat := 428
/-- `PLO_BLOB_GAS_USED`. -/ def ploBlobGasUsed : Nat := 512
/-- `PLO_EXCESS_BLOB_GAS`. -/ def ploExcessBlobGas : Nat := 520
/-- `PLO_SLOT`. -/ def ploSlot : Nat := 532

/-- `WITHDRAWAL_SIZE`. -/ def withdrawalSize : Nat := 44
/-- `PUBKEY_SIZE`. -/ def pubkeySize : Nat := 65
/-- `DEPOSIT_SIZE`. -/ def depositSize : Nat := 192
/-- `WDREQ_SIZE`. -/ def wdreqSize : Nat := 76
/-- `CONS_SIZE`. -/ def consSize : Nat := 116
/-- `BDEP_SIZE`. -/ def bdepSize : Nat := 184
/-- `BEXIT_SIZE`. -/ def bexitSize : Nat := 68

/-- `MAX_EXTRA_DATA_BYTES`. -/ def maxExtraDataBytes : Nat := 32
/-- `MAX_BYTES_PER_TRANSACTION`. -/ def maxBytesPerTransaction : Nat := 1073741824
/-- `MAX_TRANSACTIONS_PER_PAYLOAD`. -/ def maxTransactionsPerPayload : Nat := 1048576
/-- `MAX_WITHDRAWALS_PER_PAYLOAD`. -/ def maxWithdrawalsPerPayload : Nat := 16
/-- `MAX_BLOB_COMMITMENTS_PER_BLOCK`. -/ def maxBlobCommitmentsPerBlock : Nat := 4096
/-- `MAX_DEPOSIT_REQUESTS_PER_PAYLOAD`. -/ def maxDepositRequests : Nat := 8192
/-- `MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD`. -/ def maxWithdrawalRequests : Nat := 16
/-- `MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD`. -/ def maxConsolidationRequests : Nat := 2
/-- `MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD`. -/ def maxBuilderDepositRequests : Nat := 64
/-- `MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD`. -/ def maxBuilderExitRequests : Nat := 16
/-- `MAX_BLOCK_ACCESS_LIST_BYTES`. -/ def maxBlockAccessListBytes : Nat := 1073741824
/-- `MAX_WITNESS_NODES`. -/ def maxWitnessNodes : Nat := 4194304
/-- `MAX_WITNESS_CODES`. -/ def maxWitnessCodes : Nat := 262144
/-- `MAX_WITNESS_HEADERS`. -/ def maxWitnessHeaders : Nat := 256
/-- `MAX_BYTES_PER_WITNESS_NODE`. -/ def maxBytesPerWitnessNode : Nat := 1024
/-- `MAX_BYTES_PER_CODE`. -/ def maxBytesPerCode : Nat := 65536
/-- `MAX_BYTES_PER_HEADER`. -/ def maxBytesPerHeader : Nat := 1024
/-- `MAX_PUBLIC_KEYS`. -/ def maxPublicKeys : Nat := 32768

/-! ### The decode helpers of `guest/src/ssz.pnk`

The guest computes on 64-bit words with unsigned comparisons (`<+`, `>+`).
Every subtraction below is of two offsets already known to be ordered — by the
preceding `checkOffsets`, which rejects out-of-range and decreasing offsets, or
by an explicit bound — so `Nat` subtraction agrees with the guest's wrapping
subtraction, and every value involved is below `2 ^ 32`, so `Nat` comparison
agrees with the guest's unsigned comparison.
-/

/-- Nondecreasing, as `ssz_check_offsets` requires of consecutive offsets. -/
def nondecreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | first :: second :: rest => Nat.ble first second && nondecreasing (second :: rest)

/-- `ssz_check_offsets`: every variable offset in `[fixed, len]`, nondecreasing,
the first exactly `fixed`. -/
def checkOffsets (offsets : List Nat) (fixed len : Nat) : Option Unit :=
  match offsets with
  | [] => some ()
  | first :: _ =>
      if offsets.all (fun offset => Nat.ble fixed offset && Nat.ble offset len) &&
          nondecreasing offsets && first == fixed then
        some ()
      else none

/-- `ssz_split_var_list`: the slices of a serialized `List[variable, lim]` that
occupies `len` bytes at blob offset `p`, as `(offset, length)` pairs with the
offset relative to the blob. -/
def splitVarList (input : InputBlob) (p len lim : Nat) : Option (List (Nat × Nat)) := do
  if len = 0 then
    some []
  else
    guard (4 ≤ len)
    let first := le32 input p
    guard (first ≠ 0 ∧ first % 4 = 0 ∧ first ≤ len)
    let count := first / 4
    guard (count ≤ lim)
    let offsets := (List.range count).map fun index => le32 input (p + index * 4)
    guard (offsets.all fun offset => Nat.ble first offset && Nat.ble offset len)
    guard (nondecreasing offsets)
    some <| (List.range count).map fun index =>
      let offset := offsets[index]!
      (p + offset, (if index + 1 < count then offsets[index + 1]! else len) - offset)

/-- `ssz_fixed_list_count`: element count of a serialized `List[fixed size, lim]`
of `len` bytes. (`size` is a positive constant at every call site; the guest
would trap, not fail to decode, on a zero one.) -/
def fixedListCount (len size lim : Nat) : Option Nat := do
  guard (size ≠ 0)
  guard (len % size = 0)
  let count := len / size
  guard (count ≤ lim)
  some count

/-- `ssz_optional_u64`: `List[uint64, 1]`, as `(present, value)`. -/
def optionalU64 (input : InputBlob) (p len : Nat) : Option (Bool × Nat) :=
  if len = 0 then some (false, 0)
  else if len ≠ 8 then none
  else some (true, le64 input p)

/-- `decode_bytes_list`: a `List[ByteList[maxBytes], lim]`. -/
def decodeBytesList (input : InputBlob) (p len lim maxBytes : Nat) :
    Option (List (Nat × Nat)) := do
  let slices ← splitVarList input p len lim
  guard (slices.all fun slice => Nat.ble slice.2 maxBytes)
  some slices

/-! ### The decoded records -/

/-- What `decode_payload` extracts from an `SszExecutionPayload`. -/
structure Payload where
  /-- Blob offset and length of the serialized payload (`PL_RAW`, `PL_RAW_LEN`). -/
  raw : Nat × Nat
  /-- `extra_data` (`PL_EXTRA`, `PL_EXTRA_N`). -/
  extraData : Nat × Nat
  /-- The transaction slices (`PL_TXS`, `PL_TXS_N`). -/
  transactions : List (Nat × Nat)
  /-- `PL_WD_N`. -/
  withdrawalCount : Nat
  /-- Length of the `block_access_list` byte list (`PL_BAL_N`). -/
  blockAccessListLength : Nat
  /-- `PL_NUMBER`. -/ number : Nat
  /-- `PL_GAS_LIMIT`. -/ gasLimit : Nat
  /-- `PL_GAS_USED`. -/ gasUsed : Nat
  /-- `PL_TIMESTAMP`. -/ timestamp : Nat
  /-- `PL_BLOB_GAS_USED`. -/ blobGasUsed : Nat
  /-- `PL_EXCESS_BLOB_GAS`. -/ excessBlobGas : Nat
  /-- `PL_SLOT`. -/ slot : Nat
  deriving Repr, DecidableEq

/-- The five request counts of `decode_requests`. -/
structure Requests where
  /-- `REQ_DEP_N`. -/ deposits : Nat
  /-- `REQ_WDR_N`. -/ withdrawals : Nat
  /-- `REQ_CONS_N`. -/ consolidations : Nat
  /-- `REQ_BDEP_N`. -/ builderDeposits : Nat
  /-- `REQ_BEXIT_N`. -/ builderExits : Nat
  deriving Repr, DecidableEq

/-- What `decode_stateless_input` builds (`SI_*` of `guest/src/types.h`),
keeping the sizes a bound on the run would be stated in terms of. -/
structure StatelessInput where
  /-- `SI_PL`. -/ payload : Payload
  /-- `SI_VH_N`. -/ versionedHashCount : Nat
  /-- `SI_REQ`. -/ requests : Requests
  /-- `SI_STATE`, `SI_STATE_N`: the witness trie nodes. -/
  witnessState : List (Nat × Nat)
  /-- `SI_CODES`, `SI_CODES_N`. -/ witnessCodes : List (Nat × Nat)
  /-- `SI_HEADERS`, `SI_HEADERS_N`. -/ witnessHeaders : List (Nat × Nat)
  /-- `SI_CHAIN_ID`. -/ chainId : Nat
  /-- `SI_BN_SOME`, `SI_BN`. -/ blockNumberActivation : Bool × Nat
  /-- `SI_TS_SOME`, `SI_TS`. -/ timestampActivation : Bool × Nat
  /-- `SI_PK_N`. -/ publicKeyCount : Nat
  deriving Repr, DecidableEq

/-! ### The decoders -/

/-- `decode_payload`. -/
def decodePayload (input : InputBlob) (p len : Nat) : Option Payload := do
  guard (plFixed ≤ len)
  let extraOffset := le32 input (p + ploExtraOff)
  let txsOffset := le32 input (p + ploTxsOff)
  let withdrawalsOffset := le32 input (p + ploWdOff)
  let balOffset := le32 input (p + ploBalOff)
  let _ ← checkOffsets [extraOffset, txsOffset, withdrawalsOffset, balOffset] plFixed len
  guard (txsOffset - extraOffset ≤ maxExtraDataBytes)
  let transactions ← splitVarList input (p + txsOffset)
    (withdrawalsOffset - txsOffset) maxTransactionsPerPayload
  guard (transactions.all fun slice => Nat.ble slice.2 maxBytesPerTransaction)
  let withdrawalCount ← fixedListCount (balOffset - withdrawalsOffset)
    withdrawalSize maxWithdrawalsPerPayload
  guard (len - balOffset ≤ maxBlockAccessListBytes)
  some
    { raw := (p, len)
      extraData := (p + extraOffset, txsOffset - extraOffset)
      transactions
      withdrawalCount
      blockAccessListLength := len - balOffset
      number := le64 input (p + ploNumber)
      gasLimit := le64 input (p + ploGasLimit)
      gasUsed := le64 input (p + ploGasUsed)
      timestamp := le64 input (p + ploTimestamp)
      blobGasUsed := le64 input (p + ploBlobGasUsed)
      excessBlobGas := le64 input (p + ploExcessBlobGas)
      slot := le64 input (p + ploSlot) }

/-- `decode_requests`. -/
def decodeRequests (input : InputBlob) (p len : Nat) : Option Requests := do
  guard (reqFixed ≤ len)
  let offsets := (List.range 5).map fun index => le32 input (p + index * 4)
  let _ ← checkOffsets offsets reqFixed len
  let o0 := offsets[0]!
  let o1 := offsets[1]!
  let o2 := offsets[2]!
  let o3 := offsets[3]!
  let o4 := offsets[4]!
  let deposits ← fixedListCount (o1 - o0) depositSize maxDepositRequests
  let withdrawals ← fixedListCount (o2 - o1) wdreqSize maxWithdrawalRequests
  let consolidations ← fixedListCount (o3 - o2) consSize maxConsolidationRequests
  let builderDeposits ← fixedListCount (o4 - o3) bdepSize maxBuilderDepositRequests
  let builderExits ← fixedListCount (len - o4) bexitSize maxBuilderExitRequests
  some { deposits, withdrawals, consolidations, builderDeposits, builderExits }

/-- `decode_stateless_input`: the schema id, then the SSZ body. `none` on
exactly the inputs for which the guest raises `SszErr` instead of returning. -/
def decodeStatelessInput (input : InputBlob) : Option StatelessInput := do
  guard (2 ≤ input.length)
  guard (byteAt input 0 = 21 ∧ byteAt input 1 = 1)
  -- `p = p + 2; len = len - 2` past the schema id.
  let p := 2
  let len := input.length - 2
  guard (siFixed ≤ len)
  let offsets := (List.range 4).map fun index => le32 input (p + index * 4)
  let _ ← checkOffsets offsets siFixed len
  let nprOffset := offsets[0]!
  let witnessOffset := offsets[1]!
  let chainConfigOffset := offsets[2]!
  let publicKeysOffset := offsets[3]!
  -- NewPayloadRequest
  let np := p + nprOffset
  let nlen := witnessOffset - nprOffset
  guard (nprFixed ≤ nlen)
  let payloadOffset := le32 input np
  let versionedHashesOffset := le32 input (np + 4)
  let requestsOffset := le32 input (np + 40)
  let _ ← checkOffsets [payloadOffset, versionedHashesOffset, requestsOffset] nprFixed nlen
  let payload ← decodePayload input (np + payloadOffset)
    (versionedHashesOffset - payloadOffset)
  let versionedHashCount ← fixedListCount (requestsOffset - versionedHashesOffset) 32
    maxBlobCommitmentsPerBlock
  let requests ← decodeRequests input (np + requestsOffset) (nlen - requestsOffset)
  -- ExecutionWitness
  let wp := p + witnessOffset
  let wlen := chainConfigOffset - witnessOffset
  guard (12 ≤ wlen)
  let witnessOffsets := (List.range 3).map fun index => le32 input (wp + index * 4)
  let _ ← checkOffsets witnessOffsets 12 wlen
  let w0 := witnessOffsets[0]!
  let w1 := witnessOffsets[1]!
  let w2 := witnessOffsets[2]!
  let witnessState ← decodeBytesList input (wp + w0) (w1 - w0)
    maxWitnessNodes maxBytesPerWitnessNode
  let witnessCodes ← decodeBytesList input (wp + w1) (w2 - w1)
    maxWitnessCodes maxBytesPerCode
  let witnessHeaders ← decodeBytesList input (wp + w2) (wlen - w2)
    maxWitnessHeaders maxBytesPerHeader
  -- ChainConfig: [uint64 chain_id, ForkConfig]
  let cp := p + chainConfigOffset
  let clen := publicKeysOffset - chainConfigOffset
  guard (12 ≤ clen)
  let chainId := le64 input cp
  let _ ← checkOffsets [le32 input (cp + 8)] 12 clen
  -- ForkConfig: [ForkActivation]
  let fp := cp + 12
  let flen := clen - 12
  guard (4 ≤ flen)
  let _ ← checkOffsets [le32 input fp] 4 flen
  -- ForkActivation: [List[uint64, 1], List[uint64, 1]]
  let ap := fp + 4
  let alen := flen - 4
  guard (8 ≤ alen)
  let activationOffsets := [le32 input ap, le32 input (ap + 4)]
  let _ ← checkOffsets activationOffsets 8 alen
  let a0 := activationOffsets[0]!
  let a1 := activationOffsets[1]!
  let blockNumberActivation ← optionalU64 input (ap + a0) (a1 - a0)
  let timestampActivation ← optionalU64 input (ap + a1) (alen - a1)
  -- public keys: List[ByteVector[65], 2^15]
  let publicKeyCount ← fixedListCount (len - publicKeysOffset) pubkeySize maxPublicKeys
  some
    { payload
      versionedHashCount
      requests
      witnessState
      witnessCodes
      witnessHeaders
      chainId
      blockNumberActivation
      timestampActivation
      publicKeyCount }

/-- The declared block gas limit: the payload's `gas_limit` field, `none` when
the input does not decode. `Guest.declaredBlockGasLimit` is exactly this; it
lives here as well so that tools can use it without importing
`Guest.StepBound`, whose `guestPancakeStepBound` is still `sorry` and would be
forced at module initialisation. -/
def declaredGasLimit (input : InputBlob) : Option Nat :=
  (decodeStatelessInput input).map fun decoded => decoded.payload.gasLimit

end Guest.InputDecode
