#include <iostream>
#include <stdio.h>
#include <vector>
#include <queue>
#include <string>
using namespace std;

//#define DEBUG

enum STATE {
	LHS, LS, HS, S
};

const int SIZE = 12, CHOICES = 3, NumOfStates = 4, Futility = 1e9, MAX = 400000, UNDEFINED = -1;
const int Weight[NumOfStates] = {1, 1, 1, 0};
const bool AND = true, OR = false;
int globalIndex = 0;

struct Node
{
	bool solved;
	int hValue, next, choice, pos;
	vector<int> parent, cnt, Left, Right;
	vector<vector<int> > children;
	string msg;

	Node()
	: next(UNDEFINED), solved(false), cnt(NumOfStates, 0) {}

	bool isSovled(vector<Node>& AllNodes) {
		if (cnt[S] == SIZE) {
			msg = "Impossible";
			return true;	// 这里应该是不可能的情况，所以它也是对的
		}
		if (cnt[LS] == 1 && cnt[HS] == 0 && cnt[LHS] == 0) {
			msg = "Lighter";
			return true;
		}
		if (cnt[HS] == 1 && cnt[LS] == 0 && cnt[LHS] == 0) {
			msg = "Heavier";
			return true;
		}
		if (choice <= 0)
			return false;

		// 第一重是或的关系，第二重是与的关系
		for (int i = 0; i < children.size(); ++i) {
			bool OK = true;
			for (int j = 0; j < children[i].size(); ++j)
				if (!AllNodes[children[i][j]].solved) {
					OK = false;
					break;
				}
				
			if (OK) {
				/*if (pos == 3) {
					cout << "wawawawa " << i << ' ' << next << endl;
					for (int j = 0; j < children[i].size(); ++j)
						cout << "hehe: " << AllNodes[children[i][j]].solved << ' ' << children[i][j] << endl;
					int a; cin >> a;
				}*/
				next = i;
				return true;
			}
		}
		return false;
	}

	// 作为被扩展的叶节点时的评估值
	// 如果是可解节点，费用为0，否则按照h = lhs + hs + ls - 1计算h值
	void guessFare(vector<Node>& AllNodes) {
		if (isSovled(AllNodes)) {
			hValue = 0;
			solved = true;
		} else
			hValue = cnt[LHS] * Weight[LHS] + cnt[LS] * Weight[LS] + cnt[HS] * Weight[HS] + cnt[S] * Weight[S] - 1;
	}

	// 扩展完或者子节点的费用改变后，回传费用时，做重新评估自身的花费
	int eval(vector<Node>& AllNodes) {
		//cout << "hehe: " << pos << endl;

		int minFare = Futility, index = -1;
		for (int i = 0; i < children.size(); ++i) {
			int fare = 0;
			for (int j = 0; j < children[i].size(); ++j)
				fare += AllNodes[children[i][j]].hValue + 1;
			if (fare < minFare) {
				minFare = fare;
				index = i;
			}
		}

		// 要将修改及时更新到AllNodes中
		AllNodes[pos].hValue = minFare;
		return index;
	}

	// 返回值为bool，表示是否有解，虽然目前还没用到这个返回值，它只是剪枝优化的标志
	bool expandOR(vector<Node>& AllNodes) {
		Node copy(*this);
		for (int num = 1; num <= SIZE/2; ++num) {
			vector<int> left(NumOfStates, 0), right(NumOfStates, 0);
			for (int La = 0; La <= cnt[LHS]; ++La) {
				left[LHS] = La;
				for (int Ra = 0; La + Ra <= cnt[LHS]; ++Ra) {
					right[LHS] = Ra;
					for (int Lb = 0; Lb <= cnt[LS]; ++Lb) {
						left[LS] = Lb;
						for (int Rb = 0; Lb + Rb <= cnt[LS]; ++Rb) {
							right[LS] = Rb;
							for (int Lc = 0; Lc <= cnt[HS]; ++Lc) {
								left[HS] = Lc;
								for (int Rc = 0; Lc + Rc <= cnt[HS]; ++Rc) {
									right[HS] = Rc;
									int L = left[LHS] + left[LS] + left[HS] + left[S];
									int R = right[LHS] + right[LS] + right[HS] + right[S];

									if (L > num || R > num)
										continue;
									if (L != num && R != num)
										continue;
									if (L < num && cnt[S] >= num - L)
										left[S] = num - L, right[S] = 0;
									else if (R < num && cnt[S] >= num - R)
										left[S] = 0, right[S] = num - R;
									else if (!(L == num && R == num))
										continue;

									// 上面是枚举取法，下面是扩展子节点，每次三种情况，左倾，右倾和平衡
									Node child(copy);
									child.Left = left;
									child.Right = right;
									child.children.clear();
									child.parent = vector<int>(1, pos);
									child.next = UNDEFINED;
									--child.choice;
									children.push_back(child.expandAND(AllNodes));
									if (isSovled(AllNodes))
										return true;
									left[S] = right[S] = 0;		// 记得清空尾部啊
								}
							}
						}
					}
				}
			}
		}

		return false;
	}

	// 可加的优化——判断三种是否有重复的，有的话，可以去掉
	vector<int> expandAND(vector<Node>& AllNodes) {
		Node left(*this), right(*this), equal(*this);

		// case Left Heavier
		left.cnt[S] += cnt[LS] - Right[LS] + cnt[HS] - Left[HS] + (cnt[LHS] - Left[LHS] - Right[LHS]);
		left.cnt[LS] = Right[LS] + Right[LHS];
		left.cnt[HS] = Left[HS] + Left[LHS];
		left.cnt[LHS] = 0;
		left.pos = globalIndex;
		left.solved = left.isSovled(AllNodes);
		AllNodes[globalIndex++] = left;

		// case Right Heavier
		right.cnt[S] += cnt[LS] - Left[LS] + cnt[HS] - Right[HS] + (cnt[LHS] - Left[LHS] - Right[LHS]);
		right.cnt[LS] = Left[LS] + Left[LHS];
		right.cnt[HS] = Right[HS] + Right[LHS];
		right.cnt[LHS] = 0;
		right.pos = globalIndex;
		right.solved = right.isSovled(AllNodes);
		AllNodes[globalIndex++] = right;

		// case Equal
		equal.cnt[S] += Left[LS] + Right[LS] + Left[HS] + Right[HS] + Left[LHS] + Right[LHS];
		equal.cnt[LS] = cnt[LS] - Left[LS] - Right[LS];
		equal.cnt[HS] = cnt[HS] - Left[HS] - Right[HS];
		equal.cnt[LHS] = cnt[LHS] - Left[LHS] - Right[LHS];
		equal.pos = globalIndex;
		equal.solved = equal.isSovled(AllNodes);
		AllNodes[globalIndex++] = equal;

		#ifdef DEBUG
		printf("From : pos=%d, expanded\n", pos);
		this->disp();
		cout << "\tLeft:" << endl;
		left.disp();
		cout << "\tRight:" << endl;
		right.disp();
		cout << "\tEqual:" << endl;
		equal.disp();
		cout << "_____________________________" << endl;
		#endif

		vector<int> expandNodes;
		expandNodes.push_back(left.pos);
		expandNodes.push_back(right.pos);
		expandNodes.push_back(equal.pos);
		return expandNodes;
	}

	void disp() {
		printf("pos=%d, cnt: %d, %d, %d, %d\n", pos, cnt[LHS], cnt[LS], cnt[HS], cnt[S]);
		if (Left.size() > 0 && Right.size() > 0) {
			printf("Left: %d, %d, %d, %d\n", Left[LHS], Left[LS], Left[HS], Left[S]);
			printf("Right: %d, %d, %d, %d\n", Right[LHS], Right[LS], Right[HS], Right[S]);
			printf("+++++++++++++++++++++++++++++++\n");
		} else
			printf("Not expanded: %d\n", pos);
	}

	int FindNextOne(vector<Node>& AllNodes) {
		if (next == UNDEFINED)
			return pos;
		return FindNextOneHelper(AllNodes, next);
	}

	int FindNextOneHelper(vector<Node>& AllNodes, int index) {
		// 对于待扩展的局部解图，优先扩展（书里说是任意的）靠近起始节点的“非终叶节点”
		vector<int> nodes(children[index]);
		for (int i = 0; i < nodes.size(); ++i) {
			if (AllNodes[nodes[i]].next == UNDEFINED) {
				return AllNodes[nodes[i]].pos;
			}
		}

		// 如果这一层的节点都已经扩展过了，那么继续顺着还没解决的节点往下找
		// 肯定总能往下找下去，因为如果全部都有解了，那它已经被解决了
		for (int i = 0; i < nodes.size(); ++i) {
			if (!AllNodes[nodes[i]].solved) {
				return AllNodes[nodes[i]].FindNextOne(AllNodes);
			}
		}
	}
};

// 使用数组模拟链表
vector<Node> AllNodes(MAX);


bool AO_star(Node& begin) {
	// 将开始状态存入到AllNodes中，记住所有的状态都必须实时更新到AllNodes中，AllNodes相当于一张图
	begin.pos = globalIndex;
	AllNodes[globalIndex++] = begin;
	int key = begin.pos;

	while (!AllNodes[key].solved && AllNodes[key].hValue < Futility) {
		int current = AllNodes[key].FindNextOne(AllNodes); 
		Node& now = AllNodes[current];
#ifdef DEBUG
printf("Each, globalIndex=%d, current=%d\n", globalIndex, current);
#endif
		// AO*第一步，扩展子节点并评估其值
		now.expandOR(AllNodes);
		for (int i = 0; i < now.children.size(); ++i) {
			for (int j = 0; j < now.children[i].size(); ++j)
				AllNodes[now.children[i][j]].guessFare(AllNodes);
		}

#ifdef DEBUG
printf("Current=%d, children_num=%d, parent_num=%d\n", current, AllNodes[current].children.size(), AllNodes[current].parent.size());
#endif
		
		queue<int> q;
		q.push(current);
		// ?如何保证q中先出队的，一定是没有子节点在队中的
		while (!q.empty()) {
			current = q.front();	q.pop();
			Node& now2 = AllNodes[current];
			int oldFare = now2.hValue;
			int minIndex = now2.eval(AllNodes);		// 重新对自己估值
			now2.next = minIndex;
			if (now2.pos == 44)
				cout << "hhhh " << now2.next << ' ' << minIndex << endl;
			bool solved = now2.isSovled(AllNodes);
			if (now2.hValue != oldFare || solved) {
				if (solved)
					now2.solved = true;
				for (int i = 0; i < now2.parent.size(); ++i)
					q.push(now2.parent[i]);
			}
	
#ifdef DEBUG
// 待会调试完，不需要minIndex了，就可以删了它的定义，直接赋值就好了
printf("select: minIndex=%d, me=%d, q_size=%d, oldFare=%d, newFare=%d\n", minIndex, now2.pos, q.size(), oldFare, now2.hValue);
#endif
		}
		#ifdef DEBUG
		cout << "===============================\n" << endl;
		//int a; cin >> a;
		#endif

		if (AllNodes[3].solved) {
			cout << "huhu: " << AllNodes[3].next << endl;
			for (int i = 0; i < AllNodes[3].children[2].size(); ++i) {
				cout << "good? " << AllNodes[AllNodes[3].children[3][i]].solved << endl;
				AllNodes[AllNodes[3].children[3][i]].disp();
			}
			int a; cin >> a;
		}
	}

	return AllNodes[key].solved;
}

void getSolution(int me, string s) {
	Node now = AllNodes[me];
	if (now.next == UNDEFINED) {
		printf("%s(LHS=%d, LS=%d, HS=%d, S=%d, choice=%d), child=%d, pos=%d\n", 
			s.data(), now.cnt[LHS], now.cnt[LS], now.cnt[HS], now.cnt[S], now.choice, now.children.size(), now.pos);
		printf("%s%s\n", s.data(), AllNodes[me].msg.data());
		return ;
	}

	vector<int> children = now.children[now.next];
	printf("%sNow: (LHS=%d, LS=%d, HS=%d, S=%d, choice=%d)\n",
		s.data(), now.cnt[LHS], now.cnt[LS], now.cnt[HS], now.cnt[S], now.choice);

	now = AllNodes[children[0]];	// 因为pickup的信息存在子节点中，而不是自己身上
	printf("%sPickup--Left:(LHS=%d, LS=%d, HS=%d, S=%d), Right:(LHS=%d, LS=%d, HS=%d, S=%d)\n", 
		s.data(), now.Left[LHS], now.Left[LS], now.Left[HS], now.Left[S], 
		now.Right[LHS], now.Right[LS], now.Right[HS], now.Right[S]);

	char str[3][6] = {"Left", "Right", "Equal"};
	for (int i = 0; i < children.size(); ++i) {
		printf("%sCase %s: \n", s.data(), str[i]);
		getSolution(children[i], s + '\t');
	}
}

int main() {
	Node begin;
	begin.cnt[LHS] = SIZE;
	begin.choice = CHOICES;
	if (AO_star(begin)) {
		cout << "good night, jacket!" << endl;
		getSolution(0, "");
	}
	else
		cout << "Poor guy..." << endl;
	return 0;
}