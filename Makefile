# --------------------------------------------------------------------------
#
# Tiny C Compiler Makefile
#

ifndef TOP
 TOP = .
 INCLUDED = no
endif

ifeq ($(findstring $(MAKECMDGOALS),clean distclean),)
 include $(TOP)/config.mak
endif

ifeq (-$(GCC_MAJOR)-$(findstring $(GCC_MINOR),56789)-,-4--)
 CFLAGS += -D_FORTIFY_SOURCE=0
endif

LIBTCC = libtcc.a
LIBTCC1 = libtcc1.a
LINK_LIBTCC =
LIBS =
CFLAGS += $(CPPFLAGS)
VPATH = $(TOPSRC)
-LTCC = $(TOP)/$(LIBTCC)

ifdef CONFIG_WIN32
 CFG = -win
 ifneq ($(CONFIG_static),yes)
  LIBTCC = libtcc$(DLLSUF)
  LIBTCCDEF = libtcc.def
 endif
 ifneq ($(CONFIG_debug),yes)
  LDFLAGS += -s
 endif
 NATIVE_TARGET = $(ARCH)-win$(if $(findstring arm,$(ARCH)),ce,32)
else
 CFG = -unx
 LIBS+=-lm
 ifneq ($(CONFIG_ldl),no)
  LIBS+=-ldl
 endif
 ifneq ($(CONFIG_pthread),no)
  LIBS+=-lpthread
 endif
 # make libtcc as static or dynamic library?
 ifeq ($(CONFIG_static),no)
  LIBTCC=libtcc$(DLLSUF)
  export LD_LIBRARY_PATH := $(CURDIR)/$(TOP)
  ifneq ($(CONFIG_rpath),no)
    ifndef CONFIG_OSX
      LINK_LIBTCC += -Wl,-rpath,"$(libdir)"
    else
      # macOS doesn't support env-vars libdir out of the box - which we need for
      # `make test' when libtcc.dylib is used (configure --disable-static), so
      # we bake a relative path into the binary. $libdir is used after install.
      LINK_LIBTCC += -Wl,-rpath,"@executable_path/$(TOP)" -Wl,-rpath,"$(libdir)"
      # -current/compatibility_version must not contain letters.
      MACOS_DYLIB_VERSION := $(firstword $(subst rc, ,$(VERSION)))
      DYLIBVER += -current_version $(MACOS_DYLIB_VERSION)
      DYLIBVER += -compatibility_version $(MACOS_DYLIB_VERSION)
    endif
  endif
 endif
 NATIVE_TARGET = $(ARCH)
 ifdef CONFIG_OSX
  NATIVE_TARGET = $(ARCH)-osx
  ifneq ($(CC_NAME),tcc)
    LDFLAGS += -flat_namespace
    ifneq (1,$(shell expr $(GCC_MAJOR) ">=" 15))
      LDFLAGS += -undefined warning # depreciated in clang >= 15.0
    endif
  endif
  export MACOSX_DEPLOYMENT_TARGET := 10.6
 endif
endif

# run local version of tcc with local libraries and includes
TCCFLAGS-unx = -B$(TOP) -I$(TOPSRC)/include -I$(TOPSRC) -I$(TOP)
TCCFLAGS-win = -B$(TOPSRC)/win32 -I$(TOPSRC)/include -I$(TOPSRC) -I$(TOP) -L$(TOP)
TCCFLAGS = $(TCCFLAGS$(CFG))
TCC_LOCAL = $(TOP)/tcc$(EXESUF)
TCC = $(TCC_LOCAL) $(TCCFLAGS)

# run tests with the installed tcc instead
ifdef TESTINSTALL
  TCC_LOCAL = $(bindir)/tcc
  TCCFLAGS-unx = -I$(TOP)
  TCCFLAGS-win = -B$(bindir) -I$(TOP)
  -LTCC = $(libdir)/$(LIBTCC) $(LINK_LIBTCC)
endif

CFLAGS_P = $(CFLAGS) -pg -static -DCONFIG_TCC_STATIC -DTCC_PROFILE
LIBS_P = $(LIBS)
LDFLAGS_P = $(LDFLAGS)

DEF-i386           = -DTCC_TARGET_I386
DEF-i386-win32     = -DTCC_TARGET_I386 -DTCC_TARGET_PE
DEF-i386-OpenBSD   = $(DEF-i386) -DTARGETOS_OpenBSD
DEF-x86_64         = -DTCC_TARGET_X86_64
DEF-x86_64-win32   = -DTCC_TARGET_X86_64 -DTCC_TARGET_PE
DEF-x86_64-osx     = -DTCC_TARGET_X86_64 -DTCC_TARGET_MACHO
DEF-arm-fpa        = -DTCC_TARGET_ARM
DEF-arm-fpa-ld     = -DTCC_TARGET_ARM -DLDOUBLE_SIZE=12
DEF-arm-vfp        = -DTCC_TARGET_ARM -DTCC_ARM_VFP
DEF-arm-eabi       = -DTCC_TARGET_ARM -DTCC_ARM_VFP -DTCC_ARM_EABI
DEF-arm-eabihf     = $(DEF-arm-eabi) -DTCC_ARM_HARDFLOAT
DEF-arm            = $(DEF-arm-eabihf)
DEF-arm-NetBSD     = $(DEF-arm-eabihf) -DTARGETOS_NetBSD
DEF-arm-wince      = $(DEF-arm-eabihf) -DTCC_TARGET_PE
DEF-arm64          = -DTCC_TARGET_ARM64
DEF-arm64-osx      = $(DEF-arm64) -DTCC_TARGET_MACHO
DEF-arm64-FreeBSD  = $(DEF-arm64) -DTARGETOS_FreeBSD
DEF-arm64-NetBSD   = $(DEF-arm64) -DTARGETOS_NetBSD
DEF-arm64-OpenBSD  = $(DEF-arm64) -DTARGETOS_OpenBSD
DEF-riscv64        = -DTCC_TARGET_RISCV64
DEF-riscv32        = -DTCC_TARGET_RISCV32 -DTCC_RISCV_ilp32
DEF-riscv32-ilp32  = $(DEF-riscv32) -DTCC_RISCV_ilp32
DEF-c67            = -DTCC_TARGET_C67 -w # disable warnigs
DEF-x86_64-FreeBSD = $(DEF-x86_64) -DTARGETOS_FreeBSD
DEF-x86_64-NetBSD  = $(DEF-x86_64) -DTARGETOS_NetBSD
DEF-x86_64-OpenBSD = $(DEF-x86_64) -DTARGETOS_OpenBSD

ifeq ($(INCLUDED),no)
# --------------------------------------------------------------------------
# running top Makefile

PROGS = tcc$(EXESUF)
TCCLIBS = $(LIBTCCDEF) $(LIBTCC) $(LIBTCC1)
TCCDOCS = tcc.1 tcc-doc.html tcc-doc.info

all: $(PROGS) $(TCCLIBS) $(TCCDOCS)

# cross compiler targets to build
TCC_X = i386 x86_64 i386-win32 x86_64-win32 x86_64-osx arm arm64 arm-wince c67
TCC_X += riscv64 riscv32 arm64-osx
# TCC_X += arm-fpa arm-fpa-ld arm-vfp arm-eabi

# cross libtcc1.a targets to build
LIBTCC1_X = i386 x86_64 i386-win32 x86_64-win32 x86_64-osx arm arm64 arm-wince
LIBTCC1_X += riscv64 riscv32 arm64-osx

LIBTCC1_X = $(filter-out c67,$(TCC_X))

PROGS_CROSS = $(foreach X,$(TCC_X),$X-tcc$(EXESUF))
LIBTCC1_CROSS = $(foreach X,$(LIBTCC1_X),$X-libtcc1.a)

# build cross compilers & libs
cross: $(LIBTCC1_CROSS) $(PROGS_CROSS)

# build specific cross compiler & lib
cross-%: %-tcc$(EXESUF) %-libtcc1.a ;

install: ; @$(MAKE) --no-print-directory  install$(CFG)
install-strip: ; @$(MAKE) --no-print-directory  install$(CFG) CONFIG_strip=yes
uninstall: ; @$(MAKE) --no-print-directory uninstall$(CFG)

ifdef CONFIG_cross
all : cross
endif

# --------------------------------------------

T = $(or $(CROSS_TARGET),$(NATIVE_TARGET),unknown)
X = $(if $(CROSS_TARGET),$(CROSS_TARGET)-)

DEFINES += $(DEF-$T)
DEFINES += $(if $(ROOT-$T),-DCONFIG_SYSROOT="\"$(ROOT-$T)\"")
DEFINES += $(if $(CRT-$T),-DCONFIG_TCC_CRTPREFIX="\"$(CRT-$T)\"")
DEFINES += $(if $(LIB-$T),-DCONFIG_TCC_LIBPATHS="\"$(LIB-$T)\"")
DEFINES += $(if $(INC-$T),-DCONFIG_TCC_SYSINCLUDEPATHS="\"$(INC-$T)\"")
DEFINES += $(if $(ELF-$T),-DCONFIG_TCC_ELFINTERP="\"$(ELF-$T)\"")
DEFINES += $(DEF-$(or $(findstring win,$T),unx))

ifneq ($(X),)
$(if $(DEF-$T),,$(error error: unknown target: '$T'))
DEF-$(NATIVE_TARGET) =
DEF-$T += -DCONFIG_TCC_CROSSPREFIX="\"$X\""
ifneq ($(CONFIG_WIN32),yes)
DEF-win += -DCONFIG_TCCDIR="\"$(tccdir)/win32\""
endif
else
# using values from config.h
DEF-$(NATIVE_TARGET) =
endif

# include custom configuration (see make help)
-include config-extra.mak

ifneq ($(T),$(NATIVE_TARGET))
# assume support files for cross-targets in "/usr/<triplet>" by default
TRIPLET-i386 ?= i686-linux-gnu
TRIPLET-x86_64 ?= x86_64-linux-gnu
TRIPLET-arm ?= arm-linux-gnueabi
TRIPLET-arm64 ?= aarch64-linux-gnu
TRIPLET-riscv64 ?= riscv64-linux-gnu
MARCH-i386 ?= i386-linux-gnu
MARCH-$T ?= $(TRIPLET-$T)
TR = $(if $(TRIPLET-$T),$T,ignored)
CRT-$(TR) ?= /usr/$(TRIPLET-$T)/lib
LIB-$(TR) ?= {B}:/usr/$(TRIPLET-$T)/lib:/usr/lib/$(MARCH-$T)
INC-$(TR) ?= {B}/include:/usr/$(TRIPLET-$T)/include:/usr/include
endif

CORE_FILES = tcc.c tcctools.c libtcc.c tccpp.c tccgen.c tccdbg.c tccelf.c tccasm.c tccrun.c
CORE_FILES += tcc.h config.h libtcc.h tcctok.h
i386_FILES = $(CORE_FILES) i386-gen.c i386-link.c i386-asm.c i386-asm.h i386-tok.h
i386-win32_FILES = $(i386_FILES) tccpe.c
x86_64_FILES = $(CORE_FILES) x86_64-gen.c x86_64-link.c i386-asm.c x86_64-asm.h
x86_64-win32_FILES = $(x86_64_FILES) tccpe.c
x86_64-osx_FILES = $(x86_64_FILES) tccmacho.c
arm_FILES = $(CORE_FILES) arm-gen.c arm-link.c arm-asm.c arm-tok.h
arm-wince_FILES = $(arm_FILES) tccpe.c
arm-eabihf_FILES = $(arm_FILES)
arm-fpa_FILES     = $(arm_FILES)
arm-fpa-ld_FILES  = $(arm_FILES)
arm-vfp_FILES     = $(arm_FILES)
arm-eabi_FILES    = $(arm_FILES)
arm-eabihf_FILES  = $(arm_FILES)
arm64_FILES = $(CORE_FILES) arm64-gen.c arm64-link.c arm64-asm.c
arm64-osx_FILES = $(arm64_FILES) tccmacho.c
c67_FILES = $(CORE_FILES) c67-gen.c c67-link.c tcccoff.c
riscv64_FILES = $(CORE_FILES) riscv64-gen.c riscv64-link.c riscv64-asm.c
riscv32_FILES = $(CORE_FILES) riscv32-gen.c riscv32-link.c riscv32-asm.c

TCCDEFS_H$(subst yes,,$(CONFIG_predefs)) = tccdefs_.h

# libtcc sources
LIBTCC_SRC = $(filter-out tcc.c tcctools.c,$(filter %.c,$($T_FILES)))

ifeq ($(ONE_SOURCE),yes)
LIBTCC_OBJ = $(X)libtcc.o
LIBTCC_INC = $($T_FILES)
TCC_FILES = $(X)tcc.o
$(X)tcc.o $(X)libtcc.o : $(TCCDEFS_H)
else
LIBTCC_OBJ = $(patsubst %.c,$(X)%.o,$(LIBTCC_SRC))
LIBTCC_INC = $(filter %.h %-gen.c %-link.c,$($T_FILES))
TCC_FILES = $(X)tcc.o $(LIBTCC_OBJ)
$(X)tccpp.o : $(TCCDEFS_H)
$(X)libtcc.o : DEFINES += -DONE_SOURCE=0
$(CROSS_TARGET)-tcc.o : DEFINES += -DONE_SOURCE=0
endif
# native tcc always made from tcc.o and libtcc.[so|a]
tcc.o : DEFINES += -DONE_SOURCE=0
DEFINES += -I$(TOP)

GITHASH:=$(shell git rev-parse --abbrev-ref HEAD 2>/dev/null || echo no)
ifneq ($(GITHASH),no)
GITHASH:=$(shell git log -1 --date=short --pretty='format:%cd $(GITHASH)@%h')
GITMODF:=$(shell git diff --quiet || echo '*')
DEF_GITHASH:= -DTCC_GITHASH="\"$(GITHASH)$(GITMODF)\""
endif

ifeq ($(CONFIG_debug),yes)
CFLAGS += -g
LDFLAGS += -g
endif

# convert "include/tccdefs.h" to "tccdefs_.h"
%_.h : include/%.h conftest.c
	$S$(CC) -DC2STR $(filter %.c,$^) -o c2str.exe && ./c2str.exe $< $@

# target specific object rule
$(X)%.o : %.c $(LIBTCC_INC)
	$S$(CC) -o $@ -c $< $(addsuffix ,$(DEFINES) $(CFLAGS))

# additional dependencies
$(X)tcc.o : tcctools.c
$(X)tcc.o : DEFINES += $(DEF_GITHASH)

# Host Tiny C Compiler
tcc$(EXESUF): tcc.o $(LIBTCC)
	$S$(CC) -o $@ $^ $(addsuffix ,$(LIBS) $(LDFLAGS) $(LINK_LIBTCC))

# Cross Tiny C Compilers
# (the TCCDEFS_H dependency is only necessary for parallel makes,
# ala 'make -j x86_64-tcc i386-tcc tcc', which would create multiple
# c2str.exe and tccdefs_.h files in parallel, leading to access errors.
# This forces it to be made only once.  Make normally tracks multiple paths
# to the same goals and only remakes it once, but that doesn't work over
# sub-makes like in this target)
%-tcc$(EXESUF): $(TCCDEFS_H) FORCE
	@$(MAKE) --no-print-directory $@ CROSS_TARGET=$* ONE_SOURCE=$(or $(ONE_SOURCE),yes)

$(CROSS_TARGET)-tcc$(EXESUF): $(TCC_FILES)
	$S$(CC) -o $@ $^ $(LIBS) $(LDFLAGS)

# profiling version
tcc_p$(EXESUF): $($T_FILES)
	$S$(CC) -o $@ $< $(DEFINES) $(CFLAGS_P) $(LIBS_P) $(LDFLAGS_P)

# static libtcc library
libtcc.a: $(LIBTCC_OBJ)
	$S$(AR) rcs $@ $^

# dynamic libtcc library
libtcc.so: $(LIBTCC_OBJ)
	$S$(CC) -shared -Wl,-soname,$@ -o $@ $^ $(LIBS) $(LDFLAGS)

libtcc.so: override CFLAGS += -fPIC
libtcc.so: override LDFLAGS += -fPIC

# OSX dynamic libtcc library
libtcc.dylib: $(LIBTCC_OBJ)
	$S$(CC) -dynamiclib $(DYLIBVER) -install_name @rpath/$@ -o $@ $^ $(LDFLAGS) 

# OSX libtcc.dylib (without rpath/ prefix)
libtcc.osx: $(LIBTCC_OBJ)
	$S$(CC) -shared -install_name libtcc.dylib -o libtcc.dylib $^ $(LDFLAGS) 

# windows dynamic libtcc library
libtcc.dll : $(LIBTCC_OBJ)
	$S$(CC) -shared -o $@ $^ $(LDFLAGS)
libtcc.dll : DEFINES += -DLIBTCC_AS_DLL

# import file for windows libtcc.dll
libtcc.def : libtcc.dll tcc$(EXESUF)
	$S$(XTCC) -impdef $< -o $@
XTCC ?= ./tcc$(EXESUF)

# TinyCC runtime libraries
libtcc1.a : tcc$(EXESUF) FORCE
	@$(MAKE) -C lib

# Cross libtcc1.a
%-libtcc1.a : %-tcc$(EXESUF) FORCE
	@$(MAKE) -C lib CROSS_TARGET=$*

.PRECIOUS: %-libtcc1.a
FORCE:

# WHICH = which $1 2>/dev/null
# some versions of gnu-make do not recognize 'command' as a shell builtin
WHICH = sh -c 'command -v $1'

run-if = $(if $(shell $(call WHICH,$1)),$S $1 $2)
S = $(if $(findstring yes,$(SILENT)),@$(info * $@))

# --------------------------------------------------------------------------
# documentation and man page
tcc-doc.html: tcc-doc.texi
	$(call run-if,makeinfo,--no-split --html --number-sections -o $@ $<)

tcc-doc.info: tcc-doc.texi
	$(call run-if,makeinfo,$< || true)

tcc.1 : tcc-doc.pod
	$(call run-if,pod2man,--section=1 --center="Tiny C Compiler" \
		--release="$(VERSION)" $< >$@)
%.pod : %.texi
	$(call run-if,perl,$(TOPSRC)/texi2pod.pl $< $@)

doc : $(TCCDOCS)

# --------------------------------------------------------------------------
# install

INSTALL = install -m644
INSTALLBIN = install -m755 $(STRIP_$(CONFIG_strip))
STRIP_yes = -s

LIBTCC1_W = $(filter %-win32-libtcc1.a %-wince-libtcc1.a,$(LIBTCC1_CROSS))
LIBTCC1_U = $(filter-out $(LIBTCC1_W),$(wildcard *-libtcc1.a))
IB = $(if $1,$(IM) mkdir -p $2 && $(INSTALLBIN) $1 $2)
IBw = $(call IB,$(wildcard $1),$2)
IF = $(if $1,$(IM) mkdir -p $2 && $(INSTALL) $1 $2)
IFw = $(call IF,$(wildcard $1),$2)
IR = $(IM) mkdir -p $2 && cp -r $1/. $2
IM = @echo "-> $2 : $1" ;
BINCHECK = $(if $(wildcard $(PROGS) *-tcc$(EXESUF)),,@echo "Makefile: nothing found to install" && exit 1)

EXTRA_O = runmain.o bt-exe.o bt-dll.o bt-log.o bcheck.o

# install progs & libs
install-unx:
	$(call BINCHECK)
	$(call IBw,$(PROGS) *-tcc,"$(bindir)")
	$(call IFw,$(LIBTCC1) $(EXTRA_O) $(LIBTCC1_U),"$(tccdir)")
	$(call IF,$(TOPSRC)/include/*.h $(TOPSRC)/tcclib.h,"$(tccdir)/include")
	$(call $(if $(findstring .so,$(LIBTCC)),IBw,IFw),$(LIBTCC),"$(libdir)")
	$(call IF,$(TOPSRC)/libtcc.h,"$(includedir)")
	$(call IFw,tcc.1,"$(mandir)/man1")
	$(call IFw,tcc-doc.info,"$(infodir)")
	$(call IFw,tcc-doc.html,"$(docdir)")
ifneq "$(wildcard $(LIBTCC1_W))" ""
	$(call IFw,$(TOPSRC)/win32/lib/*.def $(LIBTCC1_W),"$(tccdir)/win32/lib")
	$(call IR,$(TOPSRC)/win32/include,"$(tccdir)/win32/include")
	$(call IF,$(TOPSRC)/include/*.h $(TOPSRC)/tcclib.h,"$(tccdir)/win32/include")
endif

# uninstall
uninstall-unx:
	@rm -fv $(addprefix "$(bindir)/",$(PROGS) $(PROGS_CROSS))
	@rm -fv $(addprefix "$(libdir)/", libtcc*.a libtcc*.so libtcc.dylib,$P)
	@rm -fv $(addprefix "$(includedir)/", libtcc.h)
	@rm -fv "$(mandir)/man1/tcc.1" "$(infodir)/tcc-doc.info"
	@rm -fv "$(docdir)/tcc-doc.html"
	@rm -frv "$(tccdir)"

# install progs & libs on windows
install-win:
	$(call BINCHECK)
	$(call IBw,$(PROGS) *-tcc.exe libtcc.dll,"$(bindir)")
	$(call IF,$(TOPSRC)/win32/lib/*.def,"$(tccdir)/lib")
	$(call IFw,libtcc1.a $(EXTRA_O) $(LIBTCC1_W),"$(tccdir)/lib")
	$(call IF,$(TOPSRC)/include/*.h $(TOPSRC)/tcclib.h,"$(tccdir)/include")
	$(call IR,$(TOPSRC)/win32/include,"$(tccdir)/include")
	$(call IR,$(TOPSRC)/win32/examples,"$(tccdir)/examples")
	$(call IF,$(TOPSRC)/tests/libtcc_test.c,"$(tccdir)/examples")
	$(call IFw,$(TOPSRC)/libtcc.h libtcc.def libtcc.a,"$(libdir)")
	$(call IFw,$(TOPSRC)/win32/tcc-win32.txt tcc-doc.html,"$(docdir)")
ifneq "$(wildcard $(LIBTCC1_U))" ""
	$(call IFw,$(LIBTCC1_U),"$(tccdir)/lib")
	$(call IF,$(TOPSRC)/include/*.h $(TOPSRC)/tcclib.h,"$(tccdir)/lib/include")
endif

# uninstall on windows
uninstall-win:
	@rm -fv $(foreach P,libtcc*.dll $(PROGS) *-tcc.exe,"$(bindir)"/$P)
	@rm -fr $(foreach P,doc examples include lib libtcc,"$(tccdir)"/$P/*)
	@rm -frv $(foreach P,doc examples include lib libtcc,"$(tccdir)"/$P)

# the msys-git shell works to configure && make except it does not have install
ifeq ($(OS),Windows_NT)
ifeq ($(shell $(call WHICH,install) || echo no),no)
INSTALL = cp
INSTALLBIN = cp
endif
endif

# --------------------------------------------------------------------------
# other stuff

TAGFILES = *.[ch] include/*.h lib/*.[chS]
tags : ; ctags $(TAGFILES)
# cannot have both tags and TAGS on windows
ETAGS : ; etags $(TAGFILES)

# create release tarball from *current* git branch (including tcc-doc.html
# and converting two files to CRLF)
TCC-VERSION = tcc-$(VERSION)
TCC-VERSION = tinycc-mob-$(shell git rev-parse --short=7 HEAD)
tar:    tcc-doc.html
	mkdir -p $(TCC-VERSION)
	( cd $(TCC-VERSION) && git --git-dir ../.git checkout -f )
	cp tcc-doc.html $(TCC-VERSION)
	for f in tcc-win32.txt build-tcc.bat ; do \
	    cat win32/$$f | sed 's,\(.*\),\1\r,g' > $(TCC-VERSION)/win32/$$f ; \
	done
	tar cjf $(TCC-VERSION).tar.bz2 $(TCC-VERSION)
	rm -rf $(TCC-VERSION)
	git reset

config.mak:
	$(if $(wildcard $@),,@echo "Please run ./configure." && exit 1)

# run all tests
test:
	@$(MAKE) -C tests
# run test(s) from tests2 subdir (see make help)
tests2.%:
	@$(MAKE) -C tests/tests2 $@
# run test(s) from testspp subdir (see make help)
testspp.%:
	@$(MAKE) -C tests/pp $@
# run tests with code coverage
tcov-tes% : tcc_c$(EXESUF)
	@rm -f $<.tcov
	@$(MAKE) --no-print-directory TCC_LOCAL=$(CURDIR)/$< tes$*
tcc_c$(EXESUF): $($T_FILES)
	$S$(TCC) tcc.c -o $@ -ftest-coverage $(DEFINES) $(LIBS)
# test the installed tcc instead
test-install: $(TCCDEFS_H)
	@$(MAKE) -C tests TESTINSTALL=yes #_all

clean:
	@rm -f tcc *-tcc tcc_p tcc_c
	@rm -f tags ETAGS *.o *.a *.so* *.out *.log lib*.def *.exe *.dll
	@rm -f a.out *.dylib *_.h *.pod *.tcov
	@$(MAKE) -s -C lib $@
	@$(MAKE) -s -C tests $@

distclean: clean
	@rm -vf config.h config.mak config.texi
	@rm -vf $(TCCDOCS)

.PHONY: all clean test tar tags ETAGS doc distclean install uninstall FORCE

help:
	@echo "make"
	@echo "   build native compiler (from separate objects)"
	@echo "make cross"
	@echo "   build cross compilers (from one source)"
	@echo "make ONE_SOURCE=no/yes SILENT=no/yes"
	@echo "   force building from separate/one object(s), less/more silently"
	@echo "make cross-TARGET"
	@echo "   build one specific cross compiler for 'TARGET'. Currently supported:"
	@echo "   $(wordlist 1,8,$(TCC_X))"
	@echo "   $(wordlist 9,99,$(TCC_X))"
	@echo "make test"
	@echo "   run all tests"
	@echo "make tests2.all / make tests2.37 / make tests2.37+"
	@echo "   run all/single test(s) from tests2, optionally update .expect"
	@echo "make testspp.all / make testspp.17"
	@echo "   run all/single test(s) from tests/pp"
	@echo "make tcov-test / tcov-tests2... / tcov-testspp..."
	@echo "   run tests as above with code coverage. After test(s) see tcc_c$(EXESUF).tcov"
	@echo "make test-install"
	@echo "   run tests with the installed tcc"
	@echo "Other supported make targets:"
	@echo "   install install-strip uninstall doc [dist]clean tags ETAGS tar help"
	@echo "Custom configuration:"
	@echo "   The makefile includes a file 'config-extra.mak' if it is present."
	@echo "   This file may contain some custom configuration.  For example to"
	@echo "   configure the search paths for a cross-compiler, assuming the"
	@echo "   support files in /usr/i686-linux-gnu:"
	@echo "      ROOT-i386 = /usr/i686-linux-gnu"
	@echo "      CRT-i386  = {R}/lib"
	@echo "      LIB-i386  = {B}:{R}/lib"
	@echo "      INC-i386  = {B}/include:{R}/include (*)"
	@echo "      DEF-i386  += -D__linux__"
	@echo "   Or also, for the cross platform files in /usr/<triplet>"
	@echo "      TRIPLET-i386 = i686-linux-gnu"
	@echo "   (*) tcc replaces {B} by 'tccdir' and {R} by 'CONFIG_SYSROOT'"

# --------------------------------------------------------------------------
endif # ($(INCLUDED),no)
