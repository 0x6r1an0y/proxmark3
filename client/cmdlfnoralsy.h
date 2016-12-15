//-----------------------------------------------------------------------------
//
// This code is licensed to you under the terms of the GNU GPL, version 2 or,
// at your option, any later version. See the LICENSE.txt file for the text of
// the license.
//-----------------------------------------------------------------------------
// Low frequency T55xx commands
//-----------------------------------------------------------------------------
#ifndef CMDLFNORALSY_H__
#define CMDLFNORALSY_H__
#include <string.h>
#include <inttypes.h>
#include <math.h>
#include "proxmark3.h"
#include "ui.h"
#include "util.h"
#include "graph.h"
#include "cmdparser.h"
#include "cmddata.h"
#include "cmdmain.h"
#include "cmdlf.h"
#include "protocols.h"  // for T55xx config register definitions
#include "lfdemod.h"    // parityTest
int CmdLFNoralsy(const char *Cmd);
int CmdNoralsyClone(const char *Cmd);
int CmdNoralsySim(const char *Cmd);
int CmdNoralsyRead(const char *Cmd);
int CmdNoralsyDemod(const char *Cmd);

int getnoralsyBits(uint32_t id, uint8_t *bits);

int usage_lf_noralsy_clone(void);
int usage_lf_noralsy_sim(void);
int usage_lf_noralsy_read(void);
int usage_lf_noralsy_demod(void);
#endif

