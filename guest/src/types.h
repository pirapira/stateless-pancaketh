/* types.h -- decoded record layouts (word slot indices * 8 = byte offsets).
   Mirrors SpecRef Types.lean structures; byte fields stay as pointers into
   the serialized SSZ input (which lives in the heap). */

/* Slice arrays: i-th element is <ptr, len> at arr + i*16. */
#define SLICE_PTR(arr, i) (lds 1 ((arr) + (i) * 16))
#define SLICE_LEN(arr, i) (lds 1 ((arr) + (i) * 16 + 8))

/* ExecutionPayload record */
#define PL_RAW         0     /* ptr to serialized SszExecutionPayload */
#define PL_RAW_LEN     8
#define PL_EXTRA       16    /* extra_data ptr */
#define PL_EXTRA_N     24
#define PL_TXS         32    /* slice array of transactions */
#define PL_TXS_N       40
#define PL_WD          48    /* ptr to serialized withdrawals (44 bytes each) */
#define PL_WD_N        56
#define PL_BAL         64    /* block_access_list ptr */
#define PL_BAL_N       72
#define PL_NUMBER      80
#define PL_GAS_LIMIT   88
#define PL_GAS_USED    96
#define PL_TIMESTAMP   104
#define PL_BLOB_GAS_USED 112
#define PL_EXCESS_BLOB_GAS 120
#define PL_SLOT        128
#define PL_SIZE        136
/* fixed-part byte offsets inside the serialized payload */
#define PLO_PARENT_HASH 0
#define PLO_FEE_RECIPIENT 32
#define PLO_STATE_ROOT 52
#define PLO_RECEIPTS_ROOT 84
#define PLO_LOGS_BLOOM 116
#define PLO_PREV_RANDAO 372
#define PLO_NUMBER 404
#define PLO_GAS_LIMIT 412
#define PLO_GAS_USED 420
#define PLO_TIMESTAMP 428
#define PLO_EXTRA_OFF 436
#define PLO_BASE_FEE 440
#define PLO_BLOCK_HASH 472
#define PLO_TXS_OFF 504
#define PLO_WD_OFF 508
#define PLO_BLOB_GAS_USED 512
#define PLO_EXCESS_BLOB_GAS 520
#define PLO_BAL_OFF 528
#define PLO_SLOT 532
#define PL_FIXED 540
#define WITHDRAWAL_SIZE 44

/* ExecutionRequests record: five (ptr, count) pairs of fixed-size elements */
#define REQ_DEP        0
#define REQ_DEP_N      8
#define REQ_WDR        16
#define REQ_WDR_N      24
#define REQ_CONS       32
#define REQ_CONS_N     40
#define REQ_BDEP       48
#define REQ_BDEP_N     56
#define REQ_BEXIT      64
#define REQ_BEXIT_N    72
#define REQ_SIZE       80
#define DEPOSIT_SIZE   192
#define WDREQ_SIZE     76
#define CONS_SIZE      116
#define BDEP_SIZE      184
#define BEXIT_SIZE     68
#define REQ_FIXED      20

/* StatelessInput record */
#define SI_PL          0     /* payload record ptr */
#define SI_VH          8     /* versioned hashes: ptr to n*32 bytes */
#define SI_VH_N        16
#define SI_PBBR        24    /* parent_beacon_block_root ptr (32 bytes) */
#define SI_REQ         32    /* requests record ptr */
#define SI_STATE       40    /* witness.state slice array */
#define SI_STATE_N     48
#define SI_CODES       56
#define SI_CODES_N     64
#define SI_HEADERS     72
#define SI_HEADERS_N   80
#define SI_CHAIN_ID    88
#define SI_BN_SOME     96
#define SI_BN          104
#define SI_TS_SOME     112
#define SI_TS          120
#define SI_PK          128   /* public keys: ptr to n*65 bytes */
#define SI_PK_N        136
#define SI_SIZE        144
#define PUBKEY_SIZE    65
#define NPR_FIXED      44
#define SI_FIXED       16

/* SSZ list limits (Ssz.lean) */
#define MAX_EXTRA_DATA_BYTES 32
#define MAX_BYTES_PER_TRANSACTION 1073741824
#define MAX_TRANSACTIONS_PER_PAYLOAD 1048576
#define MAX_WITHDRAWALS_PER_PAYLOAD 16
#define MAX_BLOB_COMMITMENTS_PER_BLOCK 4096
#define MAX_DEPOSIT_REQUESTS_PER_PAYLOAD 8192
#define MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD 16
#define MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD 2
#define MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD 64
#define MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD 16
#define MAX_BLOCK_ACCESS_LIST_BYTES 1073741824
#define MAX_WITNESS_NODES 4194304
#define MAX_WITNESS_CODES 262144
#define MAX_WITNESS_HEADERS 256
#define MAX_BYTES_PER_WITNESS_NODE 1024
#define MAX_BYTES_PER_CODE 65536
#define MAX_BYTES_PER_HEADER 1024
#define MAX_PUBLIC_KEYS 32768
/* chunk counts of the byte-list limits: (limit+31)/32 */
#define CHUNKS_2_30 33554432

/* Header record (Stateless.lean Header / mkHeaderFields). Byte fields are
   pointers (into the RLP payload or into computed 32-byte buffers). Scalars
   number/gasLimit/gasUsed/timestamp/blobGasUsed/excessBlobGas/slot are
   words (the reference allows wider values; wider ones are rejected —
   the guest envelope documented in Stateless.lean numericFieldWidths).
   difficulty and baseFeePerGas are U256 (4 words). */
#define HDR_IS_CURRENT     0
#define HDR_PARENT_HASH    8
#define HDR_OMMERS_HASH    16
#define HDR_COINBASE       24
#define HDR_STATE_ROOT     32
#define HDR_TX_ROOT        40
#define HDR_RECEIPT_ROOT   48
#define HDR_BLOOM          56
#define HDR_DIFFICULTY     64    /* U256 */
#define HDR_NUMBER         96
#define HDR_GAS_LIMIT      104
#define HDR_GAS_USED       112
#define HDR_TIMESTAMP      120
#define HDR_EXTRA          128
#define HDR_EXTRA_N        136
#define HDR_PREV_RANDAO    144
#define HDR_NONCE          152   /* ptr to 8 bytes */
#define HDR_BASE_FEE       160   /* U256 */
#define HDR_WITHDRAWALS_ROOT 192
#define HDR_BLOB_GAS_USED  200
#define HDR_EXCESS_BLOB_GAS 208
#define HDR_PBBR           216
#define HDR_REQUESTS_HASH  224
#define HDR_BAL_HASH       232   /* ptr, only when HDR_IS_CURRENT */
#define HDR_SLOT           240
#define HDR_SIZE           248

/* Gas constants (Gas.lean GasCosts / StateGasCosts) */
#define GAS_LIMIT_ADJUSTMENT_FACTOR 1024
#define GAS_LIMIT_MINIMUM 5000
#define GAS_PER_BLOB 131072
#define BLOB_SCHEDULE_TARGET 14
#define BLOB_SCHEDULE_MAX 21
#define BLOB_TARGET_GAS_PER_BLOCK 1835008
#define BLOB_BASE_COST 8192
#define BLOB_MIN_GASPRICE 1
#define BLOB_BASE_FEE_UPDATE_FRACTION 11684671
#define MAX_BLOB_GAS_PER_BLOCK 2752512
#define BLOB_COUNT_LIMIT 6
#define MAX_RLP_BLOCK_SIZE 8388608
