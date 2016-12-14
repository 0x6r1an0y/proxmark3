//-----------------------------------------------------------------------------
//
// This code is licensed to you under the terms of the GNU GPL, version 2 or,
// at your option, any later version. See the LICENSE.txt file for the text of
// the license.
//-----------------------------------------------------------------------------
// Low frequency T55xx commands
//-----------------------------------------------------------------------------
#ifndef CMDLFVISA2000_H__
#define CMDLFVISA2000_H__
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
int CmdLFVisa2k(const char *Cmd);
int CmdVisa2kClone(const char *Cmd);
int CmdVisa2kSim(const char *Cmd);
int CmdVisa2kRead(const char *Cmd);
int CmdVisa2kDemod(const char *Cmd);

int getvisa2kBits(uint64_t fullcode, uint8_t *bits);

int usage_lf_visa2k_clone(void);
int usage_lf_visa2k_sim(void);
int usage_lf_visa2k_read(void);
int usage_lf_visa2k_demod(void);
#endif

