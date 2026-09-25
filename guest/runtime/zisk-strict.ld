# Linker script for ZISK_STRICT_ROM=1 (see guest/build.sh).
#
# Plain `-Ttext=0x80000000 -Tdata=0xa0020000` (the default) produces an R+E
# .text PT_LOAD segment and puts the ELF/program headers in their own
# PT_LOAD segment just below .text, at 0x7ffff000. Both are accepted by
# Spike and ZisK 0.18.0, but ZisK >=1.x's stricter loader rejects the
# headers segment (outside its declared ROM window) and its riscv2zisk
# converter panics on an R+E .text segment when a second PT_LOAD segment
# (.data) is also present (reported upstream; ziskemu's own warning says it
# wants PF_X-only "for maximum performance" -- turns out it's not just
# performance).
#
# This script avoids both: headers get no PT_LOAD segment at all (PHDRS
# below has no FILEHDR/PHDRS attribute, so ld leaves them unmapped -- fine,
# nothing at runtime needs to read its own ELF header), and .text is X-only
# (FLAGS(1), no PF_R).
PHDRS
{
  text PT_LOAD FLAGS(1);
  data PT_LOAD FLAGS(6);
}
SECTIONS
{
  . = 0x80000000;
  .text : { *(.text) } :text
  . = 0xa0020000;
  .data : { *(.data) } :data
}
