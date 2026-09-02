/* config.h -- guest memory contract (see evm-asm/scripts/spike/spike_run.cc
   and guest/runtime/start.S). Pancake has no hex literals, so decimals. */
#define INPUT_ADDR       1073741824   /* 0x40000000: [8B zero meta][8B LE len][blob] */
#define INPUT_LEN_ADDR   1073741832   /* 0x40000008 */
#define INPUT_DATA_ADDR  1073741840   /* 0x40000010 */
#define OUTPUT_ADDR      2684420096   /* 0xa0010000 */
#define HEAP_BASE        2685403136   /* 0xa0100000 (= @base) */
#define HEAP_END         2952790016   /* 0xb0000000 */
#define M32              4294967295
#define WORD             8

/* Expression macros (Pancake calls are statements, not expressions). */
#define ROTR32(x, n) (((((x) >>> (n)) | ((x) << (32 - (n))))) & M32)
#define LD_LE32(p) ((ld8 (p)) | ((ld8 ((p) + 1)) << 8) | ((ld8 ((p) + 2)) << 16) | ((ld8 ((p) + 3)) << 24))
#define LD_BE32(p) (((ld8 (p)) << 24) | ((ld8 ((p) + 1)) << 16) | ((ld8 ((p) + 2)) << 8) | (ld8 ((p) + 3)))
#define LD_LE64(p) (LD_LE32(p) | (LD_LE32((p) + 4) << 32))
#define LD_BE64(p) ((LD_BE32(p) << 32) | LD_BE32((p) + 4))
