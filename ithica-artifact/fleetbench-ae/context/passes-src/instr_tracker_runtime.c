#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <signal.h>

#define MAX_BBS 100000
#define MAX_INSTR_TYPES_PER_BB 50
#define MAX_UNIQUE_INSTR_TYPES 50
#define MAX_NAME_LEN 256
#define MAX_BBS_PER_INSTR 10000

typedef struct {
    unsigned int bb_id;
    char func_name[MAX_NAME_LEN];
    char bb_name[MAX_NAME_LEN];
    unsigned long long execution_count;
    char instr_names[MAX_INSTR_TYPES_PER_BB][MAX_NAME_LEN];
    unsigned int instr_counts[MAX_INSTR_TYPES_PER_BB];
    unsigned int num_instrs;
} BBInfo;

typedef struct {
    char instr_name[MAX_NAME_LEN];
    unsigned int bb_indices[MAX_BBS_PER_INSTR];
    unsigned int num_bbs;
    unsigned int bbs_skipped;
} InstrStats;

static BBInfo bb_registry[MAX_BBS];
static unsigned int num_bbs = 0;
static pthread_mutex_t tracker_mutex = PTHREAD_MUTEX_INITIALIZER;
static volatile int report_printed = 0;

void __instr_tracker_register_bb(unsigned int bb_id, const char* func_name, const char* bb_name) {
    if (bb_id >= MAX_BBS) {
        return;
    }
    
    pthread_mutex_lock(&tracker_mutex);
    
    for (unsigned int i = 0; i < num_bbs; i++) {
        if (bb_registry[i].bb_id == bb_id && 
            strcmp(bb_registry[i].func_name, func_name) == 0 &&
            strcmp(bb_registry[i].bb_name, bb_name) == 0) {
            pthread_mutex_unlock(&tracker_mutex);
            return;
        }
    }
    
    if (num_bbs >= MAX_BBS) {
        pthread_mutex_unlock(&tracker_mutex);
        return;
    }
    
    BBInfo *info = &bb_registry[num_bbs];
    info->bb_id = bb_id;
    strncpy(info->func_name, func_name, MAX_NAME_LEN - 1);
    info->func_name[MAX_NAME_LEN - 1] = '\0';
    strncpy(info->bb_name, bb_name, MAX_NAME_LEN - 1);
    info->bb_name[MAX_NAME_LEN - 1] = '\0';
    info->execution_count = 0;
    info->num_instrs = 0;
    num_bbs++;
    
    pthread_mutex_unlock(&tracker_mutex);
}

void __instr_tracker_register_instr(unsigned int bb_id, const char* instr_name, 
                                   const char* func_name, const char* bb_name,
                                   unsigned int count) {
    pthread_mutex_lock(&tracker_mutex);
    
    BBInfo *info = NULL;
    for (unsigned int i = 0; i < num_bbs; i++) {
        if (bb_registry[i].bb_id == bb_id &&
            strcmp(bb_registry[i].func_name, func_name) == 0 &&
            strcmp(bb_registry[i].bb_name, bb_name) == 0) {
            info = &bb_registry[i];
            break;
        }
    }
    
    if (!info) {
        pthread_mutex_unlock(&tracker_mutex);
        return;
    }
    
    for (unsigned int i = 0; i < info->num_instrs; i++) {
        if (strcmp(info->instr_names[i], instr_name) == 0) {
            pthread_mutex_unlock(&tracker_mutex);
            return;
        }
    }
    
    if (info->num_instrs >= MAX_INSTR_TYPES_PER_BB) {
        pthread_mutex_unlock(&tracker_mutex);
        return;
    }
    
    strncpy(info->instr_names[info->num_instrs], instr_name, MAX_NAME_LEN - 1);
    info->instr_names[info->num_instrs][MAX_NAME_LEN - 1] = '\0';
    info->instr_counts[info->num_instrs] = count;
    info->num_instrs++;
    
    pthread_mutex_unlock(&tracker_mutex);
}

void __instr_tracker_increment(unsigned int bb_id, const char* func_name, const char* bb_name) {
    for (unsigned int i = 0; i < num_bbs; i++) {
        if (bb_registry[i].bb_id == bb_id &&
            strcmp(bb_registry[i].func_name, func_name) == 0 &&
            strcmp(bb_registry[i].bb_name, bb_name) == 0) {
            __sync_fetch_and_add(&bb_registry[i].execution_count, 1);
            return;
        }
    }
}

static int compare_bb_indices(const void *a, const void *b) {
    unsigned int idx_a = *(const unsigned int*)a;
    unsigned int idx_b = *(const unsigned int*)b;
    
    BBInfo *info_a = &bb_registry[idx_a];
    BBInfo *info_b = &bb_registry[idx_b];
    
    int cmp = strcmp(info_a->func_name, info_b->func_name);
    if (cmp != 0) return cmp;
    
    return atoi(info_a->bb_name) - atoi(info_b->bb_name);
}

static void print_report(void) {
    if (__sync_val_compare_and_swap(&report_printed, 0, 1) != 0) {
        return;
    }
    
    fprintf(stderr, "\n========================================\n");
    fprintf(stderr, "Instruction Tracker Report\n");
    fprintf(stderr, "========================================\n\n");
    
    InstrStats *instr_stats = (InstrStats *)calloc(MAX_UNIQUE_INSTR_TYPES, sizeof(InstrStats));
    if (!instr_stats) {
        fprintf(stderr, "Error: Failed to allocate memory\n");
        return;
    }
    
    unsigned int num_instr_types = 0;
    
    for (unsigned int i = 0; i < num_bbs; i++) {
        BBInfo *info = &bb_registry[i];
        
        for (unsigned int j = 0; j < info->num_instrs; j++) {
            const char *instr_name = info->instr_names[j];
            
            InstrStats *stats = NULL;
            for (unsigned int k = 0; k < num_instr_types; k++) {
                if (strcmp(instr_stats[k].instr_name, instr_name) == 0) {
                    stats = &instr_stats[k];
                    break;
                }
            }
            
            if (!stats) {
                if (num_instr_types >= MAX_UNIQUE_INSTR_TYPES) {
                    break;
                }
                stats = &instr_stats[num_instr_types];
                strncpy(stats->instr_name, instr_name, MAX_NAME_LEN - 1);
                stats->instr_name[MAX_NAME_LEN - 1] = '\0';
                stats->num_bbs = 0;
                stats->bbs_skipped = 0;
                num_instr_types++;
            }
            
            if (stats->num_bbs < MAX_BBS_PER_INSTR) {
                stats->bb_indices[stats->num_bbs] = i;
                stats->num_bbs++;
            } else {
                stats->bbs_skipped++;
            }
        }
    }
    
    for (unsigned int i = 0; i < num_instr_types; i++) {
        InstrStats *stats = &instr_stats[i];
        
        fprintf(stderr, "Instruction: %s\n", stats->instr_name);
        fprintf(stderr, "  Found in %u basic block(s):\n", stats->num_bbs);
        
        qsort(stats->bb_indices, stats->num_bbs, sizeof(unsigned int), compare_bb_indices);
        
        unsigned long long total_execs = 0;
        unsigned long long total_instances = 0;
        
        for (unsigned int j = 0; j < stats->num_bbs; j++) {
            unsigned int bb_idx = stats->bb_indices[j];
            BBInfo *info = &bb_registry[bb_idx];
            
            unsigned int static_count = 0;
            for (unsigned int k = 0; k < info->num_instrs; k++) {
                if (strcmp(info->instr_names[k], stats->instr_name) == 0) {
                    static_count = info->instr_counts[k];
                    break;
                }
            }
            
            unsigned long long exec_count = info->execution_count;
            unsigned long long total_for_bb = (unsigned long long)static_count * exec_count;
            
            fprintf(stderr, "    BB %4u: %s.BB%s\n", info->bb_id, info->func_name, info->bb_name);
            fprintf(stderr, "      - Appears in BB: %u time(s)\n", static_count);
            fprintf(stderr, "      - BB executed: %llu time(s)\n", exec_count);
            fprintf(stderr, "      - Total executions: %u × %llu = %llu\n", 
                   static_count, exec_count, total_for_bb);
            
            total_execs += exec_count;
            total_instances += total_for_bb;
        }
        
        fprintf(stderr, "  Summary:\n");
        fprintf(stderr, "    - Total BB executions: %llu\n", total_execs);
        fprintf(stderr, "    - Total instruction instances executed: %llu\n", total_instances);
        if (stats->bbs_skipped > 0) {
            fprintf(stderr, "    - Warning: %u BBs skipped\n", stats->bbs_skipped);
        }
        fprintf(stderr, "\n");
    }
    
    free(instr_stats);
    
    fprintf(stderr, "========================================\n");
    fprintf(stderr, "Total basic blocks tracked: %u\n", num_bbs);
    fprintf(stderr, "Total instruction types found: %u\n", num_instr_types);
    fprintf(stderr, "========================================\n");
}

static void signal_handler(int signum) {
    fprintf(stderr, "\n[Caught signal %d, printing report...]\n", signum);
    print_report();
    exit(0);
}

__attribute__((constructor))
static void setup_signals(void) {
    signal(SIGINT, signal_handler);
    signal(SIGTERM, signal_handler);
}

__attribute__((destructor))
static void cleanup(void) {
    print_report();
}
