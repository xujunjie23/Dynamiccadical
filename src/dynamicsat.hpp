#ifndef DYNAMICSAT_H
#define DYNAMICSAT_H

// NO CHANGES SHOULD BE MADE 
#define BOOL_CONFIG 0 
#define INT_CONFIG 1

// DynamicSAT hyperparameters
#define DSAT_SAMPLE_CNT 100000
#define DSAT_CHANGE_THRESHOLD 0.3*(stats.current.irredundant + stats.current.redundant)
#define DSAT_INT_CONFIG_STEP 0.1
#define DSAT_DECISION_CNT 100

// DynamicSAT tuneable configurations
#define DSAT_NO_CONFIGS 2
#define DSAT_NO_ACTIONS 6

extern const char* DSAT_CONFIG[DSAT_NO_CONFIGS]; 

extern const int DSAT_CONFIG_DEFAULT[DSAT_NO_CONFIGS]; 

extern const int DSAT_CONFIG_TYPE[DSAT_NO_CONFIGS]; 

extern const int DSAT_CONFIG_MAX[DSAT_NO_CONFIGS]; 

extern const int DSAT_CONFIG_MIN[DSAT_NO_CONFIGS]; 

int* dsat_get_actions(const int _action_val);

int weightedRandom(const double *weights, int no_choices);

#endif