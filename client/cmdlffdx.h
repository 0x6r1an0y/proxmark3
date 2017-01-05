//-----------------------------------------------------------------------------
//
// This code is licensed to you under the terms of the GNU GPL, version 2 or,
// at your option, any later version. See the LICENSE.txt file for the text of
// the license.
//-----------------------------------------------------------------------------
// Low frequency T55xx commands
//-----------------------------------------------------------------------------
#ifndef CMDLFFDX_H__
#define CMDLFFDX_H__
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
#include "crc16.h"		// for checksum crc-16_ccitt
#include "protocols.h"  // for T55xx config register definitions
#include "lfdemod.h"    // parityTest
int CmdLFFdx(const char *Cmd);
int CmdFdxClone(const char *Cmd);
int CmdFdxSim(const char *Cmd);
int CmdFdxRead(const char *Cmd);
int CmdFdxDemod(const char *Cmd);

int getFDXBits(uint64_t national_id, uint16_t country, uint8_t isanimal, uint8_t isextended, uint32_t extended, uint8_t *bits);

int usage_lf_fdx_clone(void);
int usage_lf_fdx_sim(void);
int usage_lf_fdx_read(void);
int usage_lf_fdx_demod(void);
#endif

