This is a continuation of riscv-32 port.

## TODOs:
Fix incorrect relocation for LA ✅

Fix incorrect relocation when initialing array with anonymous struct which contains a pointer to a global symbol ✅

Add basic operaction for long long ✅ 

Add load/store calling/returing for long long
 - Optimize calling loads, currently takes three instructions, should only be 2
 - some bugs

 Add soft floating point support

