

import numpy as np
import codecs
import matplotlib.pyplot as plt



def list_add(a,b):
    c = []
    for i in range(len(a)):
        c.append(a[i]+b[i])
    return c


def buquan(list_1, list_2):

    """
    Parameters:
    ---------------------
        list_1: list of str eg. ["run", "finish", "waiting", "run", "finish", "waiting", "run"]
        list_2: list of str eg. ["waiting", "run", "waiting", "run", "finish", "finish"]
    """


    new_list = []
    l_ex_1 = list_1[0]
    l_ex_2 = list_2[0]

    len_1 = len(list_1)
    len_2 = len(list_2)
  
    index_1 = 0
    index_2 = 0

    while index_1 < len_1 and index_2 < len_2:

        if list_1[index_1] == list_2[index_2]:
            new_list.append(list_1[index_1])
            index_1 += 1
            index_2 += 1
        else:
            new_list.append(list_1[index_1])
            index_1 += 1


    while index_1 < len_1:
        new_list.append(list_1[index_1])
        index_1 += 1

    while index_2 < len_2:
        new_list.append(list_2[index_2])
        index_2 += 1


    #print(new_list)

    return new_list


def get_max_common_threads(threads_state):

    """
    threads_state : list of list
    """
    new_list = []

    if len(threads_state) == 1:
        return threads_state[0]
 
    elif len(threads_state) == 2:
        return buquan(threads_state[0], threads_state[1])
   
    else:
        new_list = buquan(threads_state[0], threads_state[1])
        for index in range(2, len(threads_state)):
            new_list = buquan(threads_state[index], new_list)

        return new_list


def get_max_common_threads_num(threads_state, threads_state_number, new_threads_state):

    new_threads_state_number = []

    tmp_state_num = []

    i = 0
    j = 0

    for index, (state, state_num) in enumerate(zip(threads_state, threads_state_number)):

        while i < len(state) and j < len(new_threads_state):
            if state[i] == new_threads_state[j]:
                tmp_state_num.append(state_num[i])
                i += 1
                j += 1
            else:
                tmp_state_num.append(0)
                j += 1


        while j < len(new_threads_state):
            tmp_state_num.append(0)
            j += 1

        assert len(tmp_state_num) == len(new_threads_state)
        new_threads_state_number.append(tmp_state_num)
        tmp_state_num = []
        i = 0
        j = 0


    return new_threads_state_number


#f3e151 yellow
#6c3376 purle
#7f7f7f grey

def plot_thread_simulation(threads_name, new_threads_state, new_threads_state_number):

    """
    Parameters
    ----------------
    threads_name : list of str
        all threads name in one process, eg, threads1, thread2, thread3
        it matches the length of threads_state and threads_state_number
    threads_state : list of list of str
         For each state in threads_state, it contains thread state transition during simulation
    threads_state_number : list of list of int
         For each state number in threads state, it represents the duration of each state

    """

   
    ##data = np.array(new_threads_state_number)
    #data_transpose = data.transpose(data)

    new_threads_state_number = [[i[j] for i in new_threads_state_number] for j in range(len(new_threads_state_number[0]))]

    print(new_threads_state_number)

    assert len(new_threads_state_number) == len(new_threads_state)

    fig, ax =plt.subplots(figsize=(30, 10))
    ax.set_xlabel('step', fontsize=30)
    ax.set_ylabel('threads group', fontsize=30)

    starts = [0]*len(threads_name)
  
    for index, (thrd_state, thrd_data) in enumerate(zip(new_threads_state, new_threads_state_number)):
        
        #starts = [0]*len(threads_name)
        widths = []
        color_tmp = ""
        height_tmp = 0.5

        if thrd_state == "run":
            color_tmp = "lime"
            height_tmp = 0.3
        elif thrd_state == "waiting":
            color_tmp = "#f3e151"
            height_tmp = 0.3
        else:
            color_tmp = "grey"
            height_tmp = 0.02

        print(starts)
        ax.barh(threads_name, thrd_data, left=starts, height=height_tmp, color=color_tmp)

        starts = list_add(starts, thrd_data)



    fig.savefig("result")

    




if __name__=="__main__":

    list_a= []
    list_b = []
    
    list_a = ["run", "finish", "waiting", "run", "finish", "waiting", "run"]
    list_b = ["waiting", "run", "waiting", "run", "finish", "finish"]     


    threads_name = ["thread_1", "thread_2", "thread_3"]

    threads_state = [
                 ["run", "finished", "run", "finished", "run", "finished"],
                 ["waiting","run", "finished", "waiting", "run", "finished", "waiting", "run", "finished"],
                 ["waiting", "run", "waiting", "run", "waiting", "run"]
                ]  

    threads_state_number = [
                        [5, 7, 5, 7, 5, 7], 
                        [5, 3, 4, 5, 3, 4, 5, 3, 4], 
                        [8, 4, 8, 4, 8, 4]
                       ]

    for thrd in threads_state: 
        print(thrd)

    new_threads_state = get_max_common_threads(threads_state)

    print(new_threads_state)    

    new_threads_state_number = get_max_common_threads_num(threads_state, threads_state_number, new_threads_state)

    plot_thread_simulation(threads_name, new_threads_state, new_threads_state_number)
    
    print(threads_state_number)
    print(new_threads_state_number)
    #buquan(list_a, list_b) 

    
