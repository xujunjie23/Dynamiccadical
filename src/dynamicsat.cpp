#include "dynamicsat.hpp"
#include <cstdlib>

const char* DSAT_CONFIG[DSAT_NO_CONFIGS] = {//配置项名称
    "vivify", "vivifymaxeff", "vivifymineff" 
};

const int DSAT_CONFIG_DEFAULT[DSAT_NO_CONFIGS] = {//每个配置项默认值
    0, 100, 1
};

const int DSAT_CONFIG_TYPE[DSAT_NO_CONFIGS] = {//每个配置项类型
    BOOL_CONFIG, INT_CONFIG, INT_CONFIG
};

const int DSAT_CONFIG_MIN[DSAT_NO_CONFIGS] = {//最小值
    0, 10, 1
};

const int DSAT_CONFIG_MAX[DSAT_NO_CONFIGS] = {//最大值
    0, 1000, 100
};

//根据给定action_val来生成布尔和整型配置项的值
int* dsat_get_actions(const int _action_val) {//根据_action_val来确定所有配置的调整方案，_action_val一样调整方案就一样
    int action_val = _action_val;
    int* action_list = (int*)malloc(DSAT_NO_CONFIGS * sizeof(int));
    for (int i = 0; i < DSAT_NO_CONFIGS; i++) {//遍历所有配置项，
        if (DSAT_CONFIG_TYPE[i] == BOOL_CONFIG) {
            action_list[i] = action_val % 2;//布尔就对2取余来确定
            action_val /= 2;
        } else if (DSAT_CONFIG_TYPE[i] == INT_CONFIG) {
            action_list[i] = action_val % 3;//整型就对3取余来确定
            action_val /= 3;
        }
    }
    return action_list;
}

//加权随机选择
int weightedRandom(const double *weights, int no_choices) {
  double r = (double)rand() / RAND_MAX; 
  double weight_sum = 0; 
  double norm_weights[no_choices];
  for (int i = 0; i < no_choices; i++) weight_sum += weights[i]; //权重之和
  for (int i = 0; i < no_choices; i++) norm_weights[i] = weights[i] / weight_sum;//归一化，just like轮盘赌

  double cumulative_prob = 0.0;
  for (int i = 0; i < no_choices-1; i++) {
    cumulative_prob += norm_weights[i]; //累加概率，看r位于哪个动作的区间
    if (r < cumulative_prob) {
        return i; 
    }
  }
  return no_choices-1; //如果r大于所有区间，那就返回最后一个动作区间
}