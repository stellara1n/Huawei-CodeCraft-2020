# CodeCraft2020
* 队名：杰尼龟
* 成绩：江山赛区 初赛第二 复赛第一 决赛全国第七  
  
### 初赛
* 题目：有向图中找出所有长度为3~7的环。
* 方法：7+3。 对每个起始点，先从起始点反向搜索三步得到其他点到起始点的可达性。然后正向七步搜索路径，后3步利用反向可达性剪枝。

### 复赛
* 题目：在初赛基础上增加对环相邻边金额的限制。最后一天增加，金额可以是不超两位小数的浮点数，环的长度为3~8。
* 方法：改为4+4。 对每个起始点s，反向DFS四步存下所有四步路径a->b->c->d->s，以链表形式存储，每个a单独形成一个链表。如果去掉起始点s以及用于“衔接”的a，反向其实只存储了bcd这3个有效点。正向4步，通过2+3、3+3、3、4+3、4、5+3的方式分别拼出长度为5、6、3、7、4、8的环。由于得到的反向路径不是字典序，每次对所有反向路径一起排序又开销太大且没有必要，因此改为“按需排序”，当到达衔接点时，对没有排序过的衔接点所对应的反向路径，从链表中取出放到连续数组中排序并标记。以后若重复用到，可以直接到这个连续数组中找。
* 注意点：在循环中，判断的先后顺序非常重要，应当让强剪枝的判断优先；对正反向拼接时的重复节点，直接进行不等判断比每个点判vis更好，访存的开销大于数值判断；还有一些冗余判断也需要注意。

### 决赛
* 题目：有向图，计算节点的中心性（betweenness centrality），输出中心性top100的点的id及其中心性。
* 方法：算法参考Brandes U. A faster algorithm for betweenness centrality[J]. Journal of mathematical sociology, 2001, 25(2): 163-177. 大家的算法应该都一样，考察的是代码实现~~以及对数据的过过过过过拟合~~。
* 注意点：
       1）分图。决赛最后一共三个图，都有各自的特征，并且也提供了相同分布的线下数据，可以根据特征来过拟合。线上还有一个不记分的验证图，可以通过魔法判断绕过去。  
       2）cache利用，这是提升最大的，例如：根据bfs序重排节点id，使得搜索过程中前后两个点的数据更近；使用更小的数据类型，存距离从uint32改为uint16，提高cache命中率；优化数据结构，存前序节点的时候用单变量或单列数组存（由于大量点只有一个前序节点）等等。  
       3）堆的优化。决赛期间花了不少时间研究堆，试了二叉堆、八叉堆、配对堆，以及“cache堆”，包括它们的带id更新的版本。最后结果是八叉堆最优，因为8个连续的子节点对cache友好。“cache堆”重排了元素的物理地址，似乎挺好，但实际效果不好，可能是计算地址的开销太大了。不过堆的优化其实很有限，因为线上数据的距离不大，所以根据数据特征，可以对每个距离值维护一个普通队列，队列中存储id，每次取出最小的不空队列中的id就可以了，不需要优先队列。
