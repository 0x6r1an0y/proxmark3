#!/usr/bin/env python3
#-----------------------------------------------------------------------------
# Copyright (C) Proxmark3 contributors. See AUTHORS.md for details.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# See LICENSE.txt for the text of the license.
#-----------------------------------------------------------------------------
"""Compile the real GDM UID update code against an offline card/transport model."""

import argparse
import os
from pathlib import Path
import subprocess
import tempfile


PREFIX = r'''
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define MFBLOCK_SIZE 16
#define PM3_SUCCESS 0
#define PM3_EFAILED -21
#define PM3_EPARTIAL -22
#define PM3_ETIMEOUT -4
#define PM3_ETEAROFF -23
#define PM3_ECARDEXCHANGE -18
#define PM3_EWRONGANSWER -16
#define ISO14443A_CMD_READBLOCK 0x30
#define ISO14443A_CMD_WRITEBLOCK 0xA0
#define MIFARE_MAGIC_GDM_READBLOCK 0x38
#define MIFARE_MAGIC_GDM_WRITEBLOCK 0xA8
#define CMD_HF_MIFARE_WRITEBL_EX 1
#define ISO14A_CONNECT 1
#define ISO14A_CLEARTRACE 2
#define _GREEN_(value) value
#define PrintAndLogEx(level, ...) do { if (0) printf(__VA_ARGS__); } while (0)
#define sprint_hex(...) ""

typedef struct { uint8_t wakeup_type, auth_cmd, key[6]; } gdm_wakeup_t;
typedef struct { uint8_t wakeup, auth_cmd, write_cmd, block_no, key[6], block_data[16]; } mf_writeblock_ex_t;
typedef struct { int status; union { uint8_t asBytes[512]; } data; } PacketResponseNG;
typedef struct { uint8_t uidlen, uid[10]; } iso14a_card_select_t;

static uint8_t cfg[16], real0[16], hidden[2][16], original_cfg[16], original_real[16];
static mf_writeblock_ex_t pending;
static int writes, config_writes, selects, fail_write, fail_status, mismatch_write, fail_select;
static bool fail_after_apply, fail_config_read, fail_initial_read;
static int checks;

static void clearCommandBuffer(void) {}
static void DropField(void) {}
static uint8_t bcc(const uint8_t *data) { return data[0] ^ data[1] ^ data[2] ^ data[3]; }
static bool cl2(uint8_t value) { return value == 0x5A || value == 0xC3 || value == 0xA5; }

static bool selected_uid(iso14a_card_select_t *card) {
    const uint8_t *source = real0;
    uint8_t atqa = real0[6];
    card->uidlen = 4;
    if (cl2(cfg[9])) {
        source = hidden[0];
        atqa = real0[8];
        if (source[0] != 0x88 || bcc(source) != source[4] || bcc(source + 6) != source[10] ||
                source[5] != 4 || source[11] != 8) return false;
        card->uidlen = 7;
        memcpy(card->uid, source + 1, 3);
        memcpy(card->uid + 3, source + 6, 4);
    } else {
        if (cfg[9] == 0x69) { source = hidden[1]; atqa = real0[8]; }
        if (bcc(source) != source[4]) return false;
        memcpy(card->uid, source, 4);
    }
    return (atqa & 0x1F) != 0 && (atqa & 0xC0) == (card->uidlen == 7 ? 0x40 : 0);
}

static void SendIso14aReader(int flags, const void *data, int length) {
    (void)flags; (void)data; (void)length;
}
static bool WaitForIso14aReply(PacketResponseNG *response, int timeout, void *length, uint8_t *status) {
    (void)timeout; (void)length;
    iso14a_card_select_t card = {0};
    selects++;
    *status = selects == fail_select ? 0 : (selected_uid(&card) ? 2 : 3);
    if (*status == 3) card.uidlen = 0;
    memcpy(response->data.asBytes, &card, sizeof(card));
    return true;
}
static int gdm_try_read(uint8_t command, int block, const gdm_wakeup_t *wake, uint8_t *out) {
    (void)wake;
    if (fail_initial_read && writes == 0) return PM3_ETIMEOUT;
    const uint8_t *data = command == 0x30 ? real0 : hidden[block];
    memcpy(out, data, 16);
    if (writes > 0 && writes == mismatch_write) out[15] ^= 1;
    return PM3_SUCCESS;
}
static int gdm_read_config(uint8_t wake, uint8_t auth, const uint8_t *key, uint8_t *out) {
    (void)wake; (void)auth; (void)key;
    memcpy(out, cfg, 16);
    if (fail_config_read && config_writes > 0) out[15] ^= 1;
    return PM3_SUCCESS;
}
static int gdm_write_config(uint8_t wake, uint8_t auth, const uint8_t *key, const uint8_t *data) {
    (void)wake; (void)auth; (void)key;
    writes++;
    for (int i = 0; i < 16; i++) if (i != 9) assert(data[i] == original_cfg[i]);
    if (cl2(data[9])) assert(real0[8] == 0x44 && real0[9] == 0);
    if (data[9] == 0x69) assert(real0[8] == 4 && real0[9] == 0);
    if (writes == fail_write && !fail_after_apply) return fail_status;
    memcpy(cfg, data, 16);
    config_writes++;
    return writes == fail_write ? fail_status : PM3_SUCCESS;
}
static int gdm_resolve_for_write(bool gdm, bool gen1a, bool wupa, const uint8_t *key, int keylen,
                                  int read, int block, bool backdoor, const char *name,
                                  gdm_wakeup_t *wake, void *probe, void *have_probe) {
    (void)gdm; (void)gen1a; (void)wupa; (void)key; (void)keylen;
    (void)read; (void)block; (void)backdoor; (void)name; (void)probe; (void)have_probe;
    memset(wake, 0, sizeof(*wake));
    return PM3_SUCCESS;
}
static void SendCommandNG(int command, const uint8_t *data, size_t length) {
    (void)command;
    assert(length == sizeof(pending));
    memcpy(&pending, data, length);
}
static bool WaitForResponseTimeout(int command, PacketResponseNG *response, int timeout) {
    (void)command; (void)timeout;
    writes++;
    bool failure = writes == fail_write;
    if (!failure || fail_after_apply) {
        uint8_t *data = pending.write_cmd == 0xA0 ? real0 : hidden[pending.block_no];
        memcpy(data, pending.block_data, 16);
        if (pending.write_cmd == 0xA0 && cfg[9] == 0 && config_writes == 0 && pending.block_data[8] == 0x44) {
            assert(memcmp(real0, original_real, 5) == 0);
        }
    }
    response->status = failure ? fail_status : PM3_SUCCESS;
    return !failure || fail_status != PM3_ETIMEOUT;
}
'''

SUFFIX = r'''
static const uint8_t uid4[] = {0xA1, 0xB2, 0xC3, 0xD4};
static const uint8_t uid7[] = {4, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66};
static const uint8_t old7[] = {4, 0x77, 0x88, 0x99, 0xAA, 0xBB, 0xCC};

static void reset(uint8_t mode) {
    memset(cfg, 0, 16);
    memset(hidden, 0, sizeof(hidden));
    cfg[0] = 0x7A; cfg[1] = 0xFF; cfg[9] = mode; cfg[11] = cfg[12] = 0x5A; cfg[15] = 8;
    gdm_build_uid4_block((const uint8_t[]){0x11, 0x22, 0x33, 0x44}, real0);
    real0[10] = 0xAB; real0[15] = 0xCD;
    if (cl2(mode)) {
        gdm_build_uid7_hidden_block(old7, hidden[0]);
        gdm_build_uid7_block0(old7, real0);
    } else if (mode == 0x69) {
        gdm_build_uid4_block((const uint8_t[]){0x11, 0x22, 0x33, 0x44}, hidden[1]);
        real0[8] = 4;
    }
    memcpy(original_cfg, cfg, 16);
    memcpy(original_real, real0, 16);
    writes = config_writes = selects = fail_write = mismatch_write = fail_select = 0;
    fail_status = PM3_EFAILED;
    fail_after_apply = fail_config_read = fail_initial_read = false;
}

static int update(uint8_t mode) { return run_uid(mode == 0x5A ? uid7 : uid4, mode == 0x5A ? 7 : 4, mode == 0x69); }

int main(void) {
    const uint8_t old_modes[] = {0, 0x5A, 0x69, 0xC3, 0xA5};
    const uint8_t new_modes[] = {0, 0x5A, 0x69};
    for (unsigned int a = 0; a < sizeof(old_modes); a++) {
        for (unsigned int b = 0; b < sizeof(new_modes); b++) {
            reset(old_modes[a]);
            assert(update(new_modes[b]) == PM3_SUCCESS);
            iso14a_card_select_t card = {0};
            assert(selected_uid(&card));
            assert(card.uidlen == (b == 1 ? 7 : 4));
            assert(memcmp(card.uid, b == 1 ? uid7 : uid4, card.uidlen) == 0);
            if (b == 1) assert(memcmp(real0, uid7, 7) == 0 && real0[8] == 0x44);
            if (b == 0) assert(real0[6] == 4 && real0[8] == 0 && real0[9] == 0);
            if (b == 2) assert(real0[8] == 4 && memcmp(real0, original_real, 8) == 0);
            if (cl2(old_modes[a]) && b != 1) assert(memcmp(hidden[0], (uint8_t[16]){0}, 16) == 0);
            if (old_modes[a] == 0x69 && b != 2) assert(memcmp(hidden[1], (uint8_t[16]){0}, 16) == 0);
            if (cl2(old_modes[a]) && b == 1) assert(cfg[9] == old_modes[a]);
            checks++;
        }
    }
    for (int index = 1; index <= 4; index++) {
        reset(0); fail_write = index;
        assert(update(0x5A) == (index == 1 || index == 3 ? PM3_EFAILED : PM3_EPARTIAL));
        if (index <= 3) assert(config_writes == 0);
        checks++;
        for (int status = 0; status < 2; status++) {
            for (int applied = 0; applied < 2; applied++) {
                reset(0); fail_write = index; fail_status = status ? PM3_ETEAROFF : PM3_ETIMEOUT;
                fail_after_apply = applied != 0;
                assert(update(0x5A) == PM3_EPARTIAL);
                checks++;
            }
        }
    }
    for (int index = 1; index <= 4; index++) {
        if (index == 3) continue;
        reset(0); mismatch_write = index;
        assert(update(0x5A) == PM3_EPARTIAL);
        if (index < 3) assert(config_writes == 0);
        checks++;
    }
    reset(0); fail_config_read = true;
    assert(update(0x5A) == PM3_EPARTIAL); checks++;
    reset(0); fail_initial_read = true;
    assert(update(0x69) == PM3_ETIMEOUT && writes == 0); checks++;
    for (int index = 2; index <= 3; index++) {
        reset(0); fail_select = index;
        assert(update(0x69) == PM3_EPARTIAL); checks++;
    }
    reset(0x5A); fail_write = 3;
    uint8_t previous_hidden[16]; memcpy(previous_hidden, hidden[0], 16);
    assert(update(0) == PM3_EPARTIAL && memcmp(previous_hidden, hidden[0], 16) == 0); checks++;
    puts("GDM UID/ATQA regression tests passed");
    printf("%d simulated transitions and failure cases\n", checks);
    return 0;
}
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cc', default=os.environ.get('CC', 'cc'))
    parser.add_argument('--source', type=Path, help='Alternate cmdhfmf.c for regression checking')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    source = (args.source or root / 'client/src/cmdhfmf.c').read_text(encoding='utf-8')
    begin = source.index('typedef enum {\n    GDM_UID_SOURCE_BLOCK0,')
    command = source.index('static int CmdHF14AGen4_GDM_SetUid(', begin)
    body = source.index('    uint8_t old_uid[10]', command)
    end = source.index('\nstatic int gdm_wipe_write_block(', body)
    helpers = source[begin:command]
    transaction = source[body:end]
    wrapper = ('static int run_uid(const uint8_t *uid, int uidlen, bool f3d) {\n'
               '    bool gdm = false, gen1a = true, wupa = false;\n'
               '    uint8_t key[6] = {0}; int keylen = 0;\n')
    with tempfile.TemporaryDirectory(prefix='pm3-gdm-uid-') as directory:
        work = Path(directory)
        harness = work / 'test.c'
        binary = work / ('test.exe' if os.name == 'nt' else 'test')
        harness.write_text(PREFIX + helpers + wrapper + transaction + SUFFIX, encoding='utf-8')
        subprocess.run([args.cc, '-std=c11', '-Wall', '-Wextra', '-Werror',
                        str(harness), '-o', str(binary)], check=True)
        subprocess.run([str(binary)], check=True)


if __name__ == '__main__':
    main()
