#include "internal.hpp"
#include "dynamicsat.hpp"
#include "ccadical.h"  // 包含cadical_set_option声明的头文件
#include <algorithm>

#ifndef HAVE_STD_CLAMP
namespace std {
  template <typename T>
  const T& clamp(const T& v, const T& lo, const T& hi) {
    return (v < lo) ? lo : (hi < v) ? hi : v;
  }
}
#endif



namespace CaDiCaL {

// This function determines the next decision variable on the queue, without
// actually removing it from the decision queue, e.g., calling it multiple
// times without any assignment will return the same result.  This is of
// course used below in 'decide' but also in 'reuse_trail' to determine the
// largest decision level to backtrack to during 'restart' without changing
// the assigned variables (if 'opts.restartreusetrail' is non-zero).

int Internal::next_decision_variable_on_queue () {//依据队列选择下一个决策变量
  int64_t searched = 0;//统计搜索多少变量
  int res = queue.unassigned;//获取当前队列中未赋值的变量（最高优先级）
  while (val (res))//如果已经赋值，寻找下一个
    res = link (res).prev, searched++;//向前（prev）遍历队列，直到未赋值
  if (searched) {//如果进行变量搜索
    stats.searched += searched;
    update_queue_unassigned (res);//确保指向最新未赋值变量
  }
  LOG ("next queue decision variable %d bumped %" PRId64 "", res,
       bumped (res));
  return res;
}

// This function determines the best decision with respect to score.
//依据分数选择下一个变量
int Internal::next_decision_variable_with_best_score () {
  int res = 0;
  for (;;) {
    res = scores.front ();//获取最高分数变量（在队列前端）
    if (!val (res))//如果变量尚未赋值，就选它
      break;
    (void) scores.pop_front ();//否则就弹出变量，找下一个
  }
  LOG ("next decision variable %d with score %g", res, score (res));
  return res;
}

int Internal::next_decision_variable () {
  if (use_scores ())//如果启用use_scores，则启用vsids，否则就用队列
    return next_decision_variable_with_best_score ();
  else
    return next_decision_variable_on_queue ();
}

/*------------------------------------------------------------------------*/

// Implements phase saving as well using a target phase during
// stabilization unless decision phase is forced to the initial value
// of a phase is forced through the 'phase' option.

int Internal::decide_phase (int idx, bool target) {//决定给定变量idx的布尔值
  const int initial_phase = opts.phase ? 1 : -1;//根据选项设置初始相位
  int phase = 0;
  if (force_saved_phase)
    phase = phases.saved[idx];//强制使用保存相位，通常是回溯或重启时用来保存之前值
  if (!phase)//如果没有相位，尝试用forced相位，可能是某些启发式后强制设定的值
    phase = phases.forced[idx]; // swapped with opts.forcephase case!
  if (!phase && opts.forcephase)
    phase = initial_phase;//如果opts.forcephase启用，使用默认initial_phase
  if (!phase && target)
    phase = phases.target[idx];//如果target启用，使用target相位
  if (!phase)
    phase = phases.saved[idx];//最后再次尝试saved相位

  // The following should not be necessary and in some version we had even
  // a hard 'COVER' assertion here to check for this.   Unfortunately it
  // triggered for some users and we could not get to the root cause of
  // 'phase' still not being set here.  The logic for phase and target
  // saving is pretty complex, particularly in combination with local
  // search, and to avoid running in such an issue in the future again, we
  // now use this 'defensive' code here, even though such defensive code is
  // considered bad programming practice.
  //
  if (!phase)
    phase = initial_phase;//若仍未设置，使用初始相位

  return phase * idx;
}

// The likely phase of an variable used in 'collect' for optimizing
// co-location of clauses likely accessed together during search.

int Internal::likely_phase (int idx) { return decide_phase (idx, false); }//快捷确定idx最可能赋值相位，不考虑目标赋值

/*------------------------------------------------------------------------*/

// adds new level to control and trail
//
void Internal::new_trail_level (int lit) {//增加一个新的决策层
  level++;
  control.push_back (Level (lit, trail.size ()));//记录当前决策层起始位置
}

/*------------------------------------------------------------------------*/

bool Internal::satisfied () {//当前求解器是否已满足所有约束
  if ((size_t) level < assumptions.size () + (!!constraint.size ()))//level是否覆盖所有假设和约束
    return false;
  if (num_assigned < (size_t) max_var)//是否有变量未赋值
    return false;
  assert (num_assigned == (size_t) max_var);
  if (propagated < trail.size ())//所有赋值是否都已传播
    return false;
  size_t assigned = num_assigned;
  return (assigned == (size_t) max_var);//再次检查
}

bool Internal::better_decision (int lit, int other) {//比较两个变量在当前决策启发式下是更好的选择
  int lit_idx = abs (lit);//取索引
  int other_idx = abs (other);
  if (stable)
    return stab[lit_idx] > stab[other_idx];//稳定时，要活跃分数高的
  else
    return btab[lit_idx] > btab[other_idx];//不稳定是，也要分高的，但可能是其他启发式
}

// Search for the next decision and assign it to the saved phase.  Requires
// that not all variables are assigned.

//决策函数！！！！
int Internal::decide () {
  assert (!satisfied ());//新决策前，检查是否已经满足
  START (decide);//宏定义，通常用于统计时间
  int res = 0;
  //这个外部给的赋值主要用于快速测试或特定任务的测试，很明显这个求解器的外部赋值都是单文字，需要在第0层赋值好
  if ((size_t) level < assumptions.size ()) {//如果level还在assumptions阶段，说明要处理假设变量
    const int lit = assumptions[level];//取出当前层假设文字
    assert (assumed (lit));//确保有效
    const signed char tmp = val (lit);//当前赋值
    if (tmp < 0) {//lit赋值为false，违反假设，冲突，返回20UNSAT
      LOG ("assumption %d falsified", lit);
      res = 20;
    } else if (tmp > 0) {//lit赋值为true，已经被满足，不需要重新赋值
      LOG ("assumption %d already satisfied", lit);
      new_trail_level (0);
      LOG ("added pseudo decision level");
      notify_decision ();
    } else {//lit未被赋值，调用函数假设决策，推进trail
      LOG ("deciding assumption %d", lit);
      search_assume_decision (lit);//默认赋值（若为x赋值1，若为-x赋值为0）
    }
  } else if ((size_t) level == assumptions.size () && constraint.size ()) {//level刚好在assumptions时且constraint非空时，处理完索引假设变量，接下来要处理额外约束
    
    //遍历外部约束子句
    int satisfied_lit = 0;  // The literal satisfying the constrain.如果子句已满足记录使约束满足的文字
    int unassigned_lit = 0; // Highest score unassigned literal.还未满足，并有未赋值的变量，记录最高评分的未赋值文字
    int previous_lit = 0;   // Move satisfied literals to the front.用于调整约束的文字顺序，可能为了优化后续处理

    const size_t size_constraint = constraint.size ();//约束子句文字数量

#ifndef NDEBUG
    unsigned sum = 0;
    for (auto lit : constraint)
      sum += lit;
#endif
    for (size_t i = 0; i != size_constraint; i++) {//遍历约束子句中所有文字
      //获取文字，并调整constraint[i]的顺序
      // Get literal and move 'constraint[i] = constraint[i-1]'.

      int lit = constraint[i];
      constraint[i] = previous_lit;
      previous_lit = lit;
      //实现数组后移一位，给未来找到的true文字腾出第一个位置

      const signed char tmp = val (lit);
      if (tmp < 0) {
        LOG ("constraint literal %d falsified", lit);
        continue;//文字是false，继续遍历
      }

      if (tmp > 0) {
        LOG ("constraint literal %d satisfied", lit);
        satisfied_lit = lit;
        break;//有任何一个文字是true，直接跳出循环，该子句已经满足
      }

      assert (!tmp);//未赋值
      LOG ("constraint literal %d unassigned", lit);

      if (!unassigned_lit || better_decision (lit, unassigned_lit))
        unassigned_lit = lit;//若lit比unassigned_lit更好，就更新unassigned_lit为lit
    }

    if (satisfied_lit) {//子句已经满足

      constraint[0] = satisfied_lit; // Move satisfied to the front.将该文字移到最前面，后续如果要检查，第一个就找到true了，方便一点

      LOG ("literal %d satisfies constraint and "
           "is implied by assumptions",
           satisfied_lit);

      new_trail_level (0);
      LOG ("added pseudo decision level for constraint");
      notify_decision ();

    } else {
      //子句尚未满足，重新排列
      // Just move all the literals back.  If we found an unsatisfied
      // literal then it will be satisfied (most likely) at the next
      // decision and moved then to the first position.

      if (size_constraint) {
        //将constraint中文字依次往前移一位，因为第一位还空着，复原一下
        for (size_t i = 0; i + 1 != size_constraint; i++)
          constraint[i] = constraint[i + 1];

        constraint[size_constraint - 1] = previous_lit;
      }

      if (unassigned_lit) {

        LOG ("deciding %d to satisfy constraint", unassigned_lit);
        search_assume_decision (unassigned_lit);//赋值那个分最高的文字

      } else {

        LOG ("failing constraint");
        unsat_constraint = true;
        res = 20;
      }
    }

#ifndef NDEBUG
    for (auto lit : constraint)
      sum -= lit;
    assert (!sum); // Checksum of literal should not change!
#endif

  } else {

    int decision = ask_decision ();
    if ((size_t) level < assumptions.size () ||
        ((size_t) level == assumptions.size () && constraint.size ())) {
      // Forced backtrack below pseudo decision levels.
      // So one of the two branches above will handle it.
      STOP (decide);
      res = decide (); // STARTS and STOPS profiling
      START (decide);
    } else {
      stats.decisions++;//统计决策次数

      if (!decision) {
        int idx = next_decision_variable ();//选择下一个未赋值变量
        const bool target = (opts.target > 1 || (stable && opts.target));//启用极性优化策略，保持前一次赋值，或使用冲突学习得到的最佳极性
        decision = decide_phase (idx, target);//确定赋值方向
      }
      search_assume_decision (decision);//赋值会被推进到trail
    }
  }
  if (res)
    marked_failed = false;//当前路径可行
  STOP (decide);
  /************************************************************************************
    Dynamic SAT 
*************************************************************************************/

static double avg_glue = 0;
int delta_clauses_added = stats.current.redundant - last_clauses_added;
int delta_clauses_deleted = stats.reductions - last_clauses_deleted;
int change_score = delta_clauses_added + delta_clauses_deleted * 100;

if (num_decisions_D < DSAT_SAMPLE_CNT && num_decisions_D % 100 == 0) {
  if (learned)
    avg_glue = (double)tot_glue / learned;
  else
    avg_glue = 0;

  int cur_action = rand() % tot_actions;
  int* action_list = dsat_get_actions(cur_action);
  
  for (int i = 0; i < DSAT_NO_CONFIGS; i++) {
    if (DSAT_CONFIG_TYPE[i] == BOOL_CONFIG) {
      if (action_list[i] == 0) {
        cadical_set_option(&opts, DSAT_CONFIG[i], 0);
        cur_config_values[i] = 0;
      } else {
        cadical_set_option(&opts, DSAT_CONFIG[i], 1);
        cur_config_values[i] = 1;
      }
    } else if (DSAT_CONFIG_TYPE[i] == INT_CONFIG) {
      int config_value = cur_config_values[i];
      config_value += (action_list[i] - 1) * DSAT_INT_CONFIG_STEP * config_value;
  
      // clamp 替代逻辑
      if (config_value < DSAT_CONFIG_MIN[i]) {
        config_value = DSAT_CONFIG_MIN[i];
      } else if (config_value > DSAT_CONFIG_MAX[i]) {
        config_value = DSAT_CONFIG_MAX[i];
      }
  
      cadical_set_option(&opts, DSAT_CONFIG[i], config_value);
      cur_config_values[i] = config_value;
    }
  }
  

  if (last_action >= 0) {
    mab_selected_D[last_action] += 1;
    mab_reward_D[last_action] += (avg_glue > 5) ? 0 : (5 - avg_glue);
    learned = 0;
    tot_glue = 0;
  }
  last_action = cur_action;
} else if (num_decisions_D >= DSAT_SAMPLE_CNT && (change_score > DSAT_CHANGE_THRESHOLD || mab_in_process < DSAT_SAMPLE_CNT)) {
  if (change_score > DSAT_CHANGE_THRESHOLD) {
    last_clauses_added = stats.current.redundant;
    last_clauses_deleted = stats.reductions;
    mab_in_process = 0;
  } else {
    mab_in_process += 1;
    mab_in_process %= (int)1e7+1;
  }

  if (mab_in_process % DSAT_DECISION_CNT == 0) {
    if (learned)
      avg_glue = (double)tot_glue / learned;
    else
      avg_glue = 0;
  }

  int cur_action = weightedRandom(ucb_D, tot_actions);
  num_of_sampling_D += 1;
  int* action_list = dsat_get_actions(cur_action);
  
  for (int i = 0; i < DSAT_NO_CONFIGS; i++) {
    if (DSAT_CONFIG_TYPE[i] == BOOL_CONFIG) {
      if (action_list[i] == 0) {
        cadical_set_option(&opts, DSAT_CONFIG[i], 0);
        cur_config_values[i] = 0;
      } else {
        cadical_set_option(&opts, DSAT_CONFIG[i], 1);
        cur_config_values[i] = 1;
      }
    } else if (DSAT_CONFIG_TYPE[i] == INT_CONFIG) {
      int config_value = cur_config_values[i];
      config_value += (action_list[i] - 1) * DSAT_INT_CONFIG_STEP * config_value;
  
      // clamp 替代逻辑
      if (config_value < DSAT_CONFIG_MIN[i]) {
        config_value = DSAT_CONFIG_MIN[i];
      } else if (config_value > DSAT_CONFIG_MAX[i]) {
        config_value = DSAT_CONFIG_MAX[i];
      }
  
      cadical_set_option(&opts, DSAT_CONFIG[i], config_value);
      cur_config_values[i] = config_value;
    }
  }

  if (last_action >= 0) {
    mab_selected_D[last_action] += 1;
    mab_reward_D[last_action] += (avg_glue > 5) ? 0 : (5 - avg_glue);
    learned = 0;
    tot_glue = 0;
  }
  last_action = cur_action;

  for (int i = 0; i < tot_actions; i++) {
    ucb_D[i] = mab_reward_D[i] / mab_selected_D[i] + sqrt(log(num_of_sampling_D) / mab_selected_D[i]);
  }
}

num_decisions_D += 1;
unsigned tot_change_score = stats.current.redundant - last_clauses_added + (stats.reductions - last_clauses_deleted) * 100;
if (tot_change_score > mab_reset_threshold) {
  mab_reset_threshold += (stats.current.irredundant + stats.current.redundant) * 10;
  if (num_decisions_D > DSAT_SAMPLE_CNT)
    num_decisions_D = 0;
}
  return res;
}

} // namespace CaDiCaL
