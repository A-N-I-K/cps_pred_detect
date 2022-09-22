#!/usr/bin/env python
import os
import sys
import rospy
from geometry_msgs.msg import PoseStamped
from tf.transformations import euler_from_quaternion
import matplotlib.pyplot as plt
import matplotlib.cm as cm
import numpy as np
from multiprocessing import Lock, Process, Queue, current_process
import multiprocessing
import queue
import copy
import time
import csv
from z3 import *


class SMTCar:
    def __init__(self):
        rospy.init_node("SMTcar")

        #topics to monitor
        car1_pose_topic= rospy.get_param('car1_pose_topic', '/car1_30m/pf/viz/inferred_pose')
        car2_pose_topic= rospy.get_param('car2_pose_topic', '/car2_5m/pf/viz/inferred_pose')

        self.MULTIPROCESSING_ENABLED = True
        self.current_pose_car1 = None
        self.current_pose_car2 = None
        self.pose_datalist_car1= []
        self.pose_datalist_car2= []
        self.last_delta_datalist_car1=[]
        self.last_delta_datalist_car2=[]
        self. car1_delta_data =[]
        self.car2_delta_data=[]
        self.signal_length = 7.0
        self.sample_time = 0.04
        self.data_dT = rospy.get_param('data_dT',0.1)  # time interval at which to run z3 solver on the accumulated data
        self.csv_file = "data.csv"

        self.CAR1_DATA_INIT = False
        self.CAR2_DATA_INIT = False
        self.DATA_COLLECT = True
        self.FIRST_RUN = True
        self.DIVIDE_SEGMENT_N_PARTS = True
        self.MESSAGE_ENABLE = True

        #SMT solver related variables
        self.carOne_x = Function('carOne_x', IntSort(), RealSort())
        self.carOne_y = Function('carOne_y', IntSort(), RealSort())
        self.carTwo_x = Function('carTwo_x', IntSort(), RealSort())
        self.carTwo_y = Function('carTwo_y', IntSort(), RealSort())

        # Variables to be used in ordering constraint
        self.timeBefore = Int('timeBefore')
        self.timeAfter = Int('timeAfter')

        # Variables to be used for consistent cut constraint
        self.msgSend = Int('msgSend')
        self.msgReceive = Int('msgReceive')

        # Initialize happens before (between agents) function
        self.happensBefore = Function('happensBefore',IntSort(), IntSort(), IntSort(), IntSort(), BoolSort())
        # self.message_data=[[0.1,0.15,0,1],[1.2,1.25,0,1],[2.0,2.05,0,1]]
        self.total_message_data = self.prepare_message_data(50)
        self.message_data = self.total_message_data[0]


        self.eps = 1
        self.delta = 0.25
        self.deltaSquared =0.0625
        self.radius = 100
        self.diameterSquared = pow(self.radius * 2, 2)
        self.N_parts = 1

        self.start_time = 0
        self.time_eps = 0.04  #40ms

        # Publishers
        # e.g...self.cmd_vel_pub = rospy.Publisher(cmd_vel_topic, AckermannDriveStamped, queue_size=10)

        # Subscribers
        rospy.Subscriber(car1_pose_topic, PoseStamped, self.car1_pose_callback, queue_size=1)
        rospy.Subscriber(car2_pose_topic, PoseStamped, self.car2_pose_callback, queue_size=1)

    def prepare_message_data(self,qty=10):
        data_count = 1
        total_msg = []
        msg_sample = []
        margin = 0.05
        for i in range(qty):
            first_agent_sample = np.random.uniform(0, 1.0 - margin, data_count)
            second_agent_sample = np.random.uniform(0, 1.0 - margin, data_count)
            total_sample = np.concatenate((first_agent_sample, second_agent_sample))
            msg_sample = []
            for i,sample in enumerate(total_sample):
                if i<data_count:
                    temp = sample + 0.001
                    msg_sample.append([sample, temp, 0, 1])
                else:
                    temp = sample + 0.001
                    msg_sample.append([sample,temp,1,0])
            total_msg.append(msg_sample)
            data_count += 1
            # print(total_msg)
        return total_msg

    def reset_datalist(self):
        self.pose_datalist_car1 = []
        self.pose_datalist_car2 = []
        self.CAR1_DATA_INIT = False
        self.CAR2_DATA_INIT = False

    def quaternion_to_euler_yaw(self, orientation):
        _, _, yaw = euler_from_quaternion((orientation.x, orientation.y, orientation.z, orientation.w))
        return yaw

    def car1_pose_callback(self, msg):
        '''acquire estimated pose of car1 from particle filter'''
        current_yaw = self.quaternion_to_euler_yaw(msg.pose.orientation)
        self.current_pose_car1 = [msg.pose.position.x, msg.pose.position.y, current_yaw]
        if self.DATA_COLLECT:
            self.pose_datalist_car1.append(copy.deepcopy(self.current_pose_car1))
        if not self.CAR1_DATA_INIT:
            self.CAR1_DATA_INIT = True

    def car2_pose_callback(self, msg):
        '''acquire estimated pose of car2 from particle filter'''
        current_yaw = self.quaternion_to_euler_yaw(msg.pose.orientation)
        self.current_pose_car2 = [msg.pose.position.x, msg.pose.position.y, current_yaw]
        if self.DATA_COLLECT:
            self.pose_datalist_car2.append(copy.deepcopy(self.current_pose_car2))
        if not self.CAR2_DATA_INIT:
            self.CAR2_DATA_INIT = True

    def Z3abs(self,x):
        return If(x >= 0, x, -x)

    def fetch_car_datalist(self):
        car1_data = copy.deepcopy(self.pose_datalist_car1)
        car2_data = copy.deepcopy(self.pose_datalist_car2)
        print(len(car1_data), len(car2_data))
        self.reset_datalist()
        return car1_data,car2_data

    def fetch_delta_datalist(self):
        self.car1_delta_data = copy.deepcopy(self.last_delta_datalist_car1)
        self.car2_delta_data = copy.deepcopy(self.last_delta_datalist_car2)
        self.last_delta_datalist_car1 = []
        self.last_delta_datalist_car2 = []

    def update_car_datalist(self,car1_data,car2_data):
        car1_data = self.car1_delta_data + car1_data
        car2_data = self.car2_delta_data + car2_data
        return car1_data,car2_data

    def solveSMT(self,car1_data,car2_data):
        s = Solver()

        abstractTime_1 = 0
        abstractTime_2 = 0
        timestampsOne =[]
        timestampsTwo=[]

        for i in range(len(car1_data)):
            s.add(self.carOne_x(abstractTime_1) == car1_data[i][0])
            s.add(self.carOne_y(abstractTime_1) == car1_data[i][1])
            timestampsOne.append(abstractTime_1)
            abstractTime_1 += 1

        for i in range(len(car2_data)):
            s.add(self.carTwo_x(abstractTime_2) == car2_data[i][0])
            s.add(self.carTwo_y(abstractTime_2) == car2_data[i][1])
            timestampsTwo.append(abstractTime_2)
            abstractTime_2 += 1

        if self.MESSAGE_ENABLE:
            for msg in self.message_data:
                scaled_data_agent1 = int(msg[0] * 25)
                scaled_data_agent2 = int(msg[1] * 25)
                if scaled_data_agent1 < abstractTime_1 and scaled_data_agent2 < abstractTime_2:
                    s.add(self.happensBefore(scaled_data_agent1, scaled_data_agent2, msg[2], msg[3]) == True)
                else:
                    continue

        # Variables to be used for epsilon constraint
        epsOne = Int('epsOne')
        epsTwo = Int('epsTwo')
        predOne = Int('predOne')
        predTwo = Int('predTwo')

        s.add(And(epsOne >= timestampsOne[0], epsOne <= timestampsOne[-1], epsTwo >= timestampsTwo[0],
                  epsTwo <= timestampsTwo[-1]))
        s.add(And(predOne >= timestampsOne[0], predOne <= timestampsOne[-1], predTwo >= timestampsTwo[0],
                  predTwo <= timestampsTwo[-1]))

        # Re-timing function (discrete)
        rho_01 = Function('rho_01', IntSort(), IntSort())

        # Re-timing function (hybrid)
        rho_primed_01 = Function('rho_primed_01', RealSort(), RealSort())

        # Inverse re-timing function (discrete)
        rho_10 = Function('rho_10', IntSort(), IntSort())

        # Inverse re-timing function (hybrid)
        rho_primed_10 = Function('rho_primed_10', RealSort(), RealSort())

        # Variable to be used in re-timing constraint
        s_01 = Int('s_01')

        s.add(And(s_01 >= timestampsOne[0], s_01 <= timestampsOne[-1]))

        # Variable to be used in re-timing function (hybrid)
        r_01 = Real('r_01')

        # Variable to be used in inverse re-timing constraint
        s_10 = Int('s_10')

        s.add(And(s_10 >= timestampsTwo[0], s_10 <= timestampsTwo[-1]))

        # Variable to be used in inverse re-timing function (hybrid)
        r_10 = Real('r_10')

        # Variable to be used in final inverse constraint
        t_01 = Int('t_01')

        s.add(And(t_01 >= timestampsOne[0], t_01 <= timestampsOne[-1]))

        # Variables to be used in ordering constraint
        timeBefore_01 = Int('timeBefore_01')
        timeAfter_01 = Int('timeAfter_01')

        s.add(And(timeBefore_01 >= timestampsOne[0], timeBefore_01 <= timestampsOne[-1], timeAfter_01 >= timestampsOne[0], timeAfter_01 <= timestampsOne[-1]))

        # Re-timing
        s.add(ForAll(s_01, Implies(And(s_01 >= timestampsOne[0], s_01 <= timestampsOne[-1]), Or([rho_01(s_01) == timestampsTwo[i] for i in range(len(timestampsTwo))]))))

        # Inverse re-timing
        s.add(ForAll(s_10, Implies(And(s_10 >= timestampsTwo[0], s_10 <= timestampsTwo[-1]), Or([rho_10(s_10) == timestampsOne[j] for j in range(len(timestampsOne))]))))

        # Order constraint for re-timing
        s.add(ForAll([timeBefore_01, timeAfter_01], Implies(And(timeBefore_01 >= timestampsOne[0], timeBefore_01 <= timestampsOne[-1], timeAfter_01 >= timestampsOne[0], timeAfter_01 <= timestampsOne[-1], timeBefore_01 < timeAfter_01), And(rho_01(timeBefore_01) < rho_01(timeAfter_01), rho_10(timeBefore_01) < rho_10(timeAfter_01)))))

        # Epsilon constraint
        s.add(ForAll([epsOne, epsTwo], Implies(And(epsOne >= timestampsOne[0], epsOne <= timestampsOne[-1], epsTwo >= timestampsTwo[0], epsTwo <= timestampsTwo[-1], rho_01(epsOne) == epsTwo, rho_10(epsTwo) == epsOne),self.Z3abs(epsOne - epsTwo) <= self.eps)))

        # Mutual separation
        s.add(ForAll([predOne, predTwo], Implies(And(predOne >= timestampsOne[0], predOne <= timestampsOne[-1], predTwo >= timestampsTwo[0], predTwo <= timestampsTwo[-1], rho_01(predOne) == predTwo, rho_10(predTwo) == predOne), self.deltaSquared <= self.Z3SqDist2d(self.carOne_x(predOne), self.carTwo_x(predTwo), self.carOne_y(predOne), self.carTwo_y(predTwo)))))

        # Re-timing function (hybrid)
        s.add(ForAll(r_01, Implies(And(r_01 >= timestampsOne[0], r_01 <= timestampsOne[-1]), rho_primed_01(r_01) == rho_01(ToInt(r_01)) + ((r_01 - ToInt(r_01)) * (rho_01(ToInt(r_01) + 1) - rho_01(ToInt(r_01)))))))

        # Inverse re-timing function (hybrid)
        s.add(ForAll(r_10, Implies(And(r_10 >= timestampsTwo[0], r_10 <= timestampsTwo[-1]), rho_primed_10(r_10) == rho_10(ToInt(r_10)) + ((r_10 - ToInt(r_10)) * (rho_10(ToInt(r_10) + 1) - rho_10(ToInt(r_10)))))))

        # Inverse re-timing function constraint (redundant?)
        s.add(ForAll(t_01, Implies(And(t_01 >= timestampsOne[0], t_01 <= timestampsOne[-1]), rho_10(rho_01(t_01)) == t_01)))

        if self.MESSAGE_ENABLE:
            # Consistent cut constraint (two agents)
            s.add(ForAll([self.msgSend, self.msgReceive], Implies(
                And(self.msgSend >= timestampsOne[0], self.msgSend <= timestampsOne[-1],
                    self.msgReceive >= timestampsTwo[0],
                    self.msgReceive <= timestampsTwo[-1], self.happensBefore(self.msgSend, self.msgReceive,1,0),
                    self.msgReceive <= predOne),
                self.msgSend <= predTwo)))

            s.add(ForAll([self.msgSend, self.msgReceive], Implies(
                And(self.msgSend >= timestampsOne[0], self.msgSend <= timestampsOne[-1],
                    self.msgReceive >= timestampsTwo[0],
                    self.msgReceive <= timestampsTwo[-1], self.happensBefore(self.msgSend, self.msgReceive,0,1),
                    self.msgReceive <= predTwo),
                self.msgSend <= predOne)))

        # Predicate for swarm radius;
        # s.add(ForAll([t1, t2], (
        #     Implies(And(t1 >= 0, t1 < abstractTime_1, t2 >= 0, t2 < abstractTime_2, self.Z3abs(t1 - t2) <= self.eps),
        #             self.diameterSquared >= (((self.carTwo_x(t2) - self.carOne_x(t1)) * (self.carTwo_x(t2) - self.carOne_x(t1))) + (
        #                         (self.carTwo_y(t2) - self.carOne_y(t1)) * (self.carTwo_y(t2) - self.carOne_y(t1))))))))


        if self.MULTIPROCESSING_ENABLED:
            return s
        else:
            result = s.check()
            if result==unsat:
                print("Result=",result)
            # if result == sat:
            #     # Modelling
            #     m = s.model()
            #     # print(m)


    def Z3SqDist2d(self, x1, x2, y1, y2):
        return (((x2 - x1) * (x2 - x1)) + ((y2 - y1) * (y2 - y1)))

    def old_chunks(self,lst, N):
        n = int(len(lst)/N)
        div_flag=  True if len(lst)%N==0 else False
        chunk_lst= []
        for i in range(N):
            if i==N-1 and not div_flag:
                chunk_lst.append(lst[n*i:len(lst)])
            else:
                chunk_lst.append(lst[n * i:n*i+n])
        assert len(chunk_lst)==N
        return chunk_lst

    def chunks(self,lst, N):
        time_data = [0.04 * i for i in range(len(lst))]
        segl = time_data[-1]
        div_part = segl / N
        chunk_lst = []
        lower_bound = 0
        for i in range(N):
            upper_bound = div_part * (i + 1)
            temp_list = []
            for j in range(len(time_data)):
                if (time_data[j] >= lower_bound and time_data[j] < upper_bound):
                    temp_list.append(lst[j])
                elif time_data[j] > upper_bound:
                    break
                elif (time_data[j] == segl):
                    temp_list.append(lst[j])
                    break
            if temp_list == []:
                temp_list.append(chunk_lst[-1][-1])
            lower_bound = upper_bound
            chunk_lst.append(temp_list)
        return chunk_lst

    def adjust_epsilon_in_chunk(self,epsilon, chunks_lst):
        new_list = [0 for i in range(len(chunks_lst))]
        for i in range(len(chunks_lst)):
            if i == 0:
                new_list[i] = chunks_lst[i]
            elif i > 0 and i != (len(chunks_lst) - 1):
                new_list[i] = chunks_lst[i - 1][len(chunks_lst[i - 1]) - epsilon:len(chunks_lst[i - 1])] + chunks_lst[
                    i] + chunks_lst[i + 1][0:epsilon]
            elif i == len(chunks_lst) - 1:
                new_list[i] = chunks_lst[i - 1][len(chunks_lst[i - 1]) - epsilon:len(chunks_lst[i - 1])] + chunks_lst[i]
        return new_list


    def convert_string_list_to_float_list(self,data,split_characters=', '):
        strip_data = data.strip('[]')
        result = [float(idx) for idx in strip_data.split(split_characters)]
        return result

    def driverTask(self,taskToDo, taskDone,segCount,car1_data,car2_data):

        # solvers = getSMTsolvers(eps, segCount, sigDur, msgLim, 0, 1, 2, 3, 4)
        solvers = self.get_solvers_SMT(segCount, car1_data, car2_data)
        while True:
            try:
                task = taskToDo.get_nowait()  # Get task from queue
            except queue.Empty:
                break
            else:
                # doTask(task)
                result = solvers[task].check()
                taskDone.put("{} is done by {}".format(task, current_process().name))
        return True

    def multiproc_defaultSMTsolver(self, segCount, car1_data,car2_data):
        taskToDo = Queue()
        taskDone = Queue()

        taskCount = segCount
        processCount = 6  # For restricting processes to be used

        for i in range(taskCount):
            taskToDo.put(i)

        processes = []
        for i in range(processCount):
            process = Process(target=self.driverTask, args=(taskToDo, taskDone, segCount, car1_data, car2_data))
            processes.append(process)
            process.start()
        for process in processes:
            process.join()

    def read_data_and_plot(self):
        with open(self.csv_file, 'r') as read_obj:
            # pass the file object to DictReader() to get the DictReader object
            dict_reader = csv.DictReader(read_obj)
            # get a list of dictionaries from dct_reader
            list_of_dict = list(dict_reader)
            eps_list=[]
            time_list =[]
            time_list_parts=[]
            segment_list=[]
            for item in list_of_dict:
                eps_list.append(int(item['epsilon']))
                segment_list.append(self.convert_string_list_to_float_list(item['segment_list']))
                time_list.append(self.convert_string_list_to_float_list(item['time_list']))
                time_list_parts.append(self.convert_string_list_to_float_list(item['time_list_parts']))



            line_color_list =['r','g','b','y','k']
            label_list =[i*0.04 for i in eps_list]
            for i in range(len(eps_list)):
                plt.plot(segment_list[i], time_list[i], line_color_list[i], linewidth=1.5, marker='o', label=str(label_list[i]))
            plt.ylabel('Runtime in s')
            plt.xlabel('Segment length in s')
            title_txt = "Runtime vs Segment length for different values of epsilon"
            plt.title(title_txt)
            plt.legend(title="Epsilon")
            plt.show()

    def fetch_signal_length_data(self):
        start_time = time.time()
        print("Capturing signal data...")
        while not rospy.is_shutdown():
            current_time = time.time()
            if self.CAR1_DATA_INIT and self.CAR2_DATA_INIT:
                if (current_time - start_time) >= self.signal_length:
                    self.DATA_COLLECT = False
                    print("Signal data fetched")
                    return
            else:
                start_time = time.time()



    def get_chunks(self,N_parts,car1_data,car2_data):
        #divide the data into chunks
        car1_chunks = self.chunks(car1_data, N_parts)
        car2_chunks = self.chunks(car2_data, N_parts)
        #adjust the data chunk with epsilon
        car1_chunks = self.adjust_epsilon_in_chunk(int(self.eps),car1_chunks)
        car2_chunks = self.adjust_epsilon_in_chunk(int(self.eps), car2_chunks)
        return car1_chunks,car2_chunks

    def solveSMT_chunks(self,N_parts,car1_data,car2_data):
        #divide the data into chunks
        if N_parts>1:
            if N_parts > len(car1_data):
                N_parts = len(car1_data)
            car1_chunks = self.chunks(car1_data, N_parts)
            car2_chunks = self.chunks(car2_data, N_parts)
            # adjust the data chunk with epsilon
            car1_chunks = self.adjust_epsilon_in_chunk(int(self.eps), car1_chunks)
            car2_chunks = self.adjust_epsilon_in_chunk(int(self.eps), car2_chunks)
            # for each data chunk, compute smt solver and report time
            for i in range(N_parts):
                self.solveSMT(car1_chunks[i], car2_chunks[i])
        else:
            self.solveSMT(car1_data,car2_data)

    def get_solvers_SMT(self,N_parts,car1_data,car2_data):
        #divide the data into chunks
        solvers = []
        if N_parts>1:
            if N_parts>len(car1_data):
                N_parts = len(car1_data)
            car1_chunks = self.chunks(car1_data, N_parts)
            car2_chunks = self.chunks(car2_data, N_parts)
            #adjust the data chunk with epsilon
            car1_chunks = self.adjust_epsilon_in_chunk(int(self.eps),car1_chunks)
            car2_chunks = self.adjust_epsilon_in_chunk(int(self.eps), car2_chunks)
            #for each data chunk, compute smt solver and report time
            for i in range(N_parts):
                solvers.append(self.solveSMT(car1_chunks[i],car2_chunks[i]))
        else:
            solvers.append(self.solveSMT(car1_data,car2_data))
        return solvers


    def write_to_csv_file(self,file_name,csv_columns,columns_data):
        dict_data={}
        for i in range(len(csv_columns)):
            dict_data.update({csv_columns[i]: columns_data[i]})

        self.csv_file = file_name
        dirname = os.path.dirname(__file__)
        file_name = os.path.join(dirname, self.csv_file)
        file_exists = os.path.isfile(file_name)
        try:
            with open(self.csv_file, 'w') as csvfile:
                writer = csv.DictWriter(csvfile, fieldnames=csv_columns)
                if not file_exists:
                    writer.writeheader()
                writer.writerow(dict_data)
        except IOError:
            print("I/O error")

    def vary_segment_length(self,car1_data,car2_data,n_chops=1,return_flag=False):
        self.N_parts=n_chops
        start_seg = 0.4
        seg_interval = 0.2  #0.5
        segment_list = [start_seg+seg_interval*i for i in range(9)]  #9
        print(segment_list)
        self.eps = 0.001
        seg_time_list = []
        for segl in segment_list:
            #break down the total signal into signal duration
            print("Segment length=", segl)
            self.start_time = time.time()
            data_count = int(segl * 25)
            car1_chunks,car2_chunks = car1_data[0:data_count],car2_data[0:data_count]
            if self.MULTIPROCESSING_ENABLED:
                self.multiproc_defaultSMTsolver(self.N_parts, car1_chunks, car2_chunks)
            else:
                self.solveSMT_chunks(self.N_parts,car1_chunks, car2_chunks)
            seg_solve_time = time.time()-self.start_time
            print("data-count:", data_count)
            print(seg_solve_time)
            seg_time_list.append(seg_solve_time)
        if return_flag:
            return segment_list,seg_time_list
        else:
            csv_columns = ['signal_length', 'total_time_list', 'epsilon']
            csv_data = []
            csv_data.append(segment_list)
            csv_data.append(seg_time_list)
            csv_data.append(self.eps)
            self.write_to_csv_file('time_vs_signal_length.csv', csv_columns, csv_data)
            self.plot_segment_data(segment_list,seg_time_list)

    def vary_epsilon(self,car1_data,car2_data,segment_length=2.0,n_chops=1,return_flag=False):
        segl= segment_length   #fixed segment length
        self.N_parts = n_chops
        start_eps = 0.001
        eps_interval = 0.0001
        eps_list = [start_eps + eps_interval * i for i in range(41)]
        eps_time_list = []
        for idx,eps in enumerate(eps_list):
            # break down the total signal into signal duration
            print("Epsilon=", eps)
            self.eps = eps
            self.start_time = time.time()
            data_count = int(segl * 25)
            print("data-count:", data_count)
            offset = 60
            car1_chunks, car2_chunks = car1_data[offset:data_count+offset], car2_data[offset-int(self.eps):data_count+offset]
            if self.MULTIPROCESSING_ENABLED:
                self.multiproc_defaultSMTsolver(self.N_parts, car1_chunks, car2_chunks)
            else:
                self.solveSMT_chunks(self.N_parts, car1_chunks, car2_chunks)
            solve_time = time.time() - self.start_time
            print(solve_time)
            eps_time_list.append(solve_time)
        if return_flag:
            return eps_list,eps_time_list
        else:
            csv_columns = ['epsilon', 'total_time_list', 'signal_length']
            csv_data = []
            csv_data.append(eps_list)
            csv_data.append(eps_time_list)
            csv_data.append(segl)
            self.write_to_csv_file('time_vs_epsilon.csv', csv_columns, csv_data)
            self.plot_epsilon_data(eps_list, eps_time_list)

    def vary_communication(self,car1_data,car2_data,segment_length=2.0,n_chops=1,return_flag=False):
        segl= segment_length   #fixed segment length
        self.N_parts = n_chops
        no_messages_per_agent = 51
        self.total_message_data = self.prepare_message_data(no_messages_per_agent-1)
        print(len(self.total_message_data))
        start_msg_length = 0   #1 per second
        incr_interval = 1
        msg_list = [start_msg_length + incr_interval * i for i in range(no_messages_per_agent)]
        print(msg_list)
        self.eps = 0.001
        msg_time_list = []
        msg_data_idx=0
        for idx in range(len(msg_list)):
            # break down the total signal into signal duration
            print("Msg=", msg_list[idx])
            if msg_list[idx]==0:
                self.MESSAGE_ENABLE = False
            else:
                self.MESSAGE_ENABLE = True
                self.message_data = self.total_message_data[msg_data_idx]
                msg_data_idx +=1
            self.start_time = time.time()
            data_count = int(segl * 25)
            print("data-count:", data_count)
            car1_chunks,car2_chunks = car1_data[0:data_count],car2_data[0:data_count]
            if self.MULTIPROCESSING_ENABLED:
                self.multiproc_defaultSMTsolver(self.N_parts, car1_chunks, car2_chunks)
            else:
                self.solveSMT_chunks(self.N_parts, car1_chunks, car2_chunks)
            solve_time = time.time() - self.start_time
            print(solve_time)
            msg_time_list.append(solve_time)
        if return_flag:
            return msg_list,msg_time_list
        else:
            csv_columns = ['epsilon', 'total_time_list', 'signal_length']
            csv_data = []
            csv_data.append(msg_list)
            csv_data.append(msg_time_list)
            csv_data.append(segl)
            self.write_to_csv_file('time_vs_communication.csv', csv_columns, csv_data)
            self.plot_communication_data(msg_list, msg_time_list)

    def vary_chopping(self,car1_data,car2_data,segment_length=4.0,eps=0.001,return_flag=False):
        segl = segment_length  # fixed segment length
        self.eps = eps  #fixed epsilon
        print("Segment length=", segl , "Epsilon=",self.time_eps)
        # n_chops_list = [8+i for i in range(33)]  #33
        n_chops_list = [4 + 2*i for i in range(11)]  # 33
        print(n_chops_list)
        time_list = []
        for n in n_chops_list:
            self.N_parts = n
            # break down the total signal into signal duration
            self.start_time = time.time()
            data_count = int(segl * 25)
            print("data-count:", data_count)
            car1_chunks, car2_chunks = car1_data[0:data_count], car2_data[0:data_count]
            if self.MULTIPROCESSING_ENABLED:
                self.multiproc_defaultSMTsolver(self.N_parts, car1_chunks, car2_chunks)
            else:
                self.solveSMT_chunks(self.N_parts, car1_chunks, car2_chunks)
            solve_time = time.time() - self.start_time
            print(solve_time)
            time_list.append(solve_time)
        if not return_flag:
            csv_columns = ['n_segments', 'total_time_list','signal_length','epsilon']
            csv_data = []
            csv_data.append(n_chops_list)
            csv_data.append(time_list)
            csv_data.append(segl)
            csv_data.append(self.time_eps)
            self.write_to_csv_file('time_vs_segments.csv', csv_columns, csv_data)
            self.plot_chop_data(n_chops_list, time_list)
        else:
            return n_chops_list,time_list

    def vary_chopping_with_segment(self, car1_data, car2_data, eps=0.001,iterations=5):
        start_seg = 0.5
        seg_interval = 0.1  # 0.5
        segment_list = [start_seg + seg_interval * i for i in range(6)]  # 9

        segment_list.append(2)
        self.MESSAGE_ENABLE = False
        print(segment_list)
        total_time_list = []
        n_chops_list=None
        variance_list = []
        for segl in segment_list:
            temp_time_list=[]
            for idx in range(iterations):
                n_chops_list,time_list = self.vary_chopping(car1_data,car2_data,segl,eps,return_flag=True)
                temp_time_list.append(time_list)
            variance_list.append(np.var(temp_time_list, axis=0).tolist())
            final_time_list = np.average(temp_time_list, axis=0).tolist()
            total_time_list.append(copy.deepcopy(final_time_list))

        csv_columns = ['n_segments', 'total_time_list', 'signal_length','variance_data']
        csv_data=[]
        csv_data.append(n_chops_list)
        csv_data.append(total_time_list)
        csv_data.append(segment_list)
        csv_data.append(variance_list)
        self.write_to_csv_file('time_vs_segments_for_signal_length.csv',csv_columns,csv_data)

        line_color_list = ['r', 'g', 'b', 'y', 'k','m','c'] #'c'
        label_list = [i for i in segment_list]
        for i in range(len(segment_list)):
            plt.plot(n_chops_list, np.log10(total_time_list[i]), line_color_list[i], linewidth=1.5, marker='o',
                     label=str(label_list[i]))
            if i == 0 or i ==(len(segment_list)-1):
                for x, y in zip(n_chops_list, total_time_list[i]):
                    label = "{:.2f}".format(y)
                    plt.annotate(label,  # this is the text
                                 (x, np.log10(y)),  # this is the point to label
                                 textcoords="offset points",  # how to position the text
                                 xytext=(0, 10),  # distance from text to points (x,y)
                                 ha='center')  # horizontal alignment can be left, right or center
        plt.xticks(n_chops_list)
        plt.ylabel('Runtime in log2(y) s')
        plt.xlabel('Number of Segments')
        title_txt = "Runtime vs number of segments for different values of signal length"
        plt.title(title_txt)
        plt.legend(title="Signal length")
        plt.grid()
        plt.show()
        return n_chops_list, total_time_list, segment_list


    def vary_segment_with_chopping(self, car1_data, car2_data):
        n_chops_list = [1, 3, 6, 8, 10]
        total_time_list = []
        for n_chop in n_chops_list:
            seg_list,time_list = self.vary_segment_length(car1_data,car2_data,n_chops=n_chop,return_flag=True)
            total_time_list.append(time_list)

        line_color_list = ['r', 'g', 'b', 'y', 'k']
        label_list = [i for i in n_chops_list]
        for i in range(len(n_chops_list)):
            plt.plot(seg_list, total_time_list[i], line_color_list[i], linewidth=1.5, marker='o',
                     label=str(label_list[i]))
            if i==0 or i==4:
                for x, y in zip(seg_list, total_time_list[i]):
                    label = "{:.2f}".format(y)
                    plt.annotate(label,  # this is the text
                                 (x, y),  # this is the point to label
                                 textcoords="offset points",  # how to position the text
                                 xytext=(0, 10),  # distance from text to points (x,y)
                                 ha='center')  # horizontal alignment can be left, right or center

        csv_columns = ['signal_length', 'total_time_list', 'n_segments']
        csv_data = []
        csv_data.append(seg_list)
        csv_data.append(total_time_list)
        csv_data.append(n_chops_list)
        self.write_to_csv_file('time_vs_signal_length_for_segments.csv', csv_columns, csv_data)

        plt.ylabel('Runtime in s')
        plt.xlabel('Signal length')
        title_txt = "Runtime vs Signal Length for different number of Segments"
        plt.title(title_txt)
        plt.legend(title="Number of segments")
        plt.grid()
        plt.show()
        return seg_list, total_time_list, n_chops_list

    def vary_chopping_with_epsilon(self, car1_data, car2_data, segl=2.0,iterations=5):
        # n_chops_list = [1,2,3,4,5,6,7,8,9,10,20]
        n_chops_list = [1,2,3,4,5,7,9,20]
        total_time_list = []
        eps_list=None
        variance_list=[]
        for n_chop in n_chops_list:
            temp_time_list = []
            for idx in range(iterations):
                print("iterations:",idx)
                eps_list,time_list = self.vary_epsilon(car1_data,car2_data,segment_length=segl,n_chops=n_chop,return_flag=True)
                temp_time_list.append(time_list)
            variance_list.append(np.var(temp_time_list,axis=0).tolist())
            final_time_list = np.average(temp_time_list, axis=0).tolist()
            total_time_list.append(copy.deepcopy(final_time_list))

        csv_columns = ['epsilon', 'total_time_list', 'n_segments','variance_data']
        csv_data = []
        csv_data.append(eps_list)
        csv_data.append(total_time_list)
        csv_data.append(n_chops_list)
        csv_data.append(variance_list)
        self.write_to_csv_file('time_vs_epsilon_for_segments.csv', csv_columns, csv_data)

        line_color_list = ['r', 'g', 'b', 'y', 'k','c', 'm', '#64ff33', '#44118e', '#1bb9b7','#d34f19']#'+--'
        label_list = [i for i in n_chops_list]
        # eps_list = np.array(eps_list) * 0.04
        eps_list = np.array(eps_list) * 1000

        for i in range(len(n_chops_list)):
            log_time_list = np.log2(total_time_list[i])
            plt.plot(eps_list, log_time_list, line_color_list[i], linewidth=1.5,
                     label=str(label_list[i]))
            label_variance_data = (np.array(variance_list[i]) * 1000).tolist()
            for x, ylog ,y,v in zip(eps_list, log_time_list,total_time_list[i],label_variance_data):
                label_time = "{:.2f}".format(y)
                label_var = "'{:.2f}'".format(v)

                plt.annotate(label_time,  # this is the text
                             (x, ylog),  # this is the point to label
                             textcoords="offset points",  # how to position the text
                             xytext=(0, 10),  # distance from text to points (x,y)
                             ha='center')  # horizontal alignment can be left, right or center
                plt.annotate(label_var,  # this is the text
                             (x, ylog),  # this is the point to label
                             textcoords="offset points",  # how to position the text
                             xytext=(0, -10),  # distance from text to points (x,y)
                             ha='center')  # horizontal alignment can be left, right or center
            # self.plot_variance_data(eps_list,total_time_list[i],variance_list[i],color_region=line_color_list[i])
        plt.xticks(eps_list)
        plt.ylabel('Runtime in log2(y) s')
        plt.xlabel('Epsilon')
        title_txt = "Runtime vs Epsilon for different number of segments"
        plt.title(title_txt)
        plt.legend(title="Number of segments")
        plt.grid()
        plt.show()
        return eps_list,total_time_list,n_chops_list

    def vary_communication_repeat(self, car1_data, car2_data, segl=1, segments=1, iterations=5):
        total_time_list = []
        for i in range(iterations):
            print("Iterations=",i+1)
            msg_list,time_list = self.vary_communication(car1_data, car2_data, segment_length=segl, n_chops=segments, return_flag=True)
            total_time_list.append(time_list)

        variance_list = np.var(total_time_list,axis=0).tolist()
        final_time_list = np.average(total_time_list, axis=0).tolist()
        csv_columns = ['messages', 'total_time_list', 'signal_length','variance_list']
        csv_data = []
        csv_data.append(msg_list)
        csv_data.append(final_time_list)
        csv_data.append(segl)
        csv_data.append(variance_list)

        self.write_to_csv_file('time_vs_communication.csv', csv_columns, csv_data)
        self.plot_communication_data(msg_list, final_time_list,variance_list)



    def vary_epsilon_repeat(self, car1_data, car2_data, segl=1, segments=1, iterations=5):
        total_time_list = []
        for i in range(iterations):
            print("Iterations=",i+1)
            eps_list, time_list = self.vary_epsilon(car1_data, car2_data, segment_length=segl, n_chops=segments,
                                                    return_flag=True)
            total_time_list.append(time_list)

        variance_list = np.var(total_time_list, axis=0).tolist()
        final_time_list = np.average(total_time_list, axis=0).tolist()
        csv_columns = ['epsilon', 'total_time_list', 'signal_length','variance_list']
        csv_data = []
        csv_data.append(eps_list)
        csv_data.append(final_time_list)
        csv_data.append(segl)
        csv_data.append(variance_list)
        self.write_to_csv_file('time_vs_epsilon.csv', csv_columns, csv_data)
        self.plot_epsilon_data(eps_list, final_time_list)


    def find_best_segment_count(self,car1_data, car2_data,eps):
        start_seg = 0.5
        seg_interval = 0.5  # 0.5
        segment_list = [start_seg + seg_interval * i for i in range(12)]  # 9
        print(segment_list)
        self.MESSAGE_ENABLE = False
        total_time_list = []
        n_chops_list = None
        best_segment_list = []
        best_segment_time_list=[]
        iterations=5
        for segl in segment_list:
            temp_time_list = []
            for idx in range(iterations):
                print("iterations:", idx)
                n_chops_list, time_list = self.vary_chopping(car1_data, car2_data, segl, eps, return_flag=True)
                temp_time_list.append(time_list)
            final_time_list = np.average(temp_time_list, axis=0).tolist()
            best_segment_idx = np.argmin(final_time_list)
            best_segment_list.append(n_chops_list[int(best_segment_idx)])
            best_segment_time_list.append(final_time_list[int(best_segment_idx)])
            total_time_list.append(copy.deepcopy(final_time_list))
        print("signal lengths=",segment_list)
        print("best segments count=",best_segment_list)
        self.plot_best_segment_data(segment_list,best_segment_time_list,best_segment_list)


    def run_SMT_node(self):
        # desired_data_count = int(self.signal_length / self.sample_time)
        self.fetch_signal_length_data()
        print(len(self.pose_datalist_car1),len(self.pose_datalist_car2))
        min_len = min(len(self.pose_datalist_car1),len(self.pose_datalist_car2))
        car1_data = self.pose_datalist_car1[0:min_len]
        car2_data = self.pose_datalist_car2[0:min_len]

        self.vary_segment_length(car1_data,car2_data,n_chops=4,return_flag=False)
        # self.vary_epsilon(car1_data,car2_data,segment_length=1.5,n_chops=1,return_flag=False)
        # self.vary_communication_repeat( car1_data, car2_data, segl=1, segments=10, iterations=2)
        # self.vary_epsilon_repeat(car1_data, car2_data, segl=2, segments=10, iterations=10)

        # self.vary_chopping(car1_data,car2_data,segment_length=2.0,eps=0.001)
        # self.vary_chopping_with_segment(car1_data,car2_data,eps=1,iterations=2)
        # self.vary_chopping_with_epsilon(car1_data,car2_data,segl=2.0,iterations=1)
        # self.vary_segment_with_chopping(car1_data,car2_data)
        # self.find_best_segment_count(car1_data,car2_data,eps=0.001)
        rospy.spin()

    def plot_epsilon_data(self,x_data,y_data):
        x_data = np.array(x_data)*1000
        plt.plot(x_data, y_data, 'b', linewidth=1.5, marker='o')
        for x, y in zip(x_data, y_data):
            label = "{:.2f}".format(y)
            plt.annotate(label,  # this is the text
                         (x, y),  # this is the point to label
                         textcoords="offset points",  # how to position the text
                         xytext=(0, 10),  # distance from text to points (x,y)
                         ha='center')  # horizontal alignment can be left, right or center
        plt.xticks(x_data)
        plt.ylabel('Runtime in s')
        plt.xlabel('Epsilon in ms')
        plt.title("Runtime vs Epsilon(Signal length = 2.0)")
        plt.grid()
        plt.show()

    def plot_communication_data(self,x_data,y_data,variance_data):
        print(variance_data)
        x_data=[2*i for i in x_data]
        plt.plot(x_data, y_data, 'b', linewidth=1.5, marker='o')
        label_variance_data = (np.array(variance_data)*1000).tolist()
        for x,y,v in zip(x_data, y_data, label_variance_data):
            label_time = "{:.2f}".format(y)
            label_var = "'{:.2f}'".format(v)

            plt.annotate(label_time,  # this is the text
                         (x, y),  # this is the point to label
                         textcoords="offset points",  # how to position the text
                         xytext=(0, 10),  # distance from text to points (x,y)
                         ha='center')  # horizontal alignment can be left, right or center
            plt.annotate(label_var,  # this is the text
                         (x, y),  # this is the point to label
                         textcoords="offset points",  # how to position the text
                         xytext=(0, -10),  # distance from text to points (x,y)
                         ha='center')  # horizontal alignment can be left, right or center
        self.plot_variance_data(x_data, y_data, variance_data, color_region='#d34f19')
        plt.xticks(x_data)
        plt.ylabel('Runtime in s')
        plt.xlabel('Communication (Total Messages)')
        plt.title("Runtime vs Communication(Signal length = 1.0)")
        plt.grid()
        plt.show()

    def plot_variance_data(self,x_data,y_data,variance_data,color_region='r'):
        upper_range = np.array(y_data) + np.array(variance_data)
        lower_range = np.array(y_data) - np.array(variance_data)
        plt.fill_between(x_data, lower_range, upper_range, alpha=0.4, linewidth=0, color=color_region)

    def plot_chop_data(self,x_data,y_data):
        plt.plot(x_data, y_data, 'r', linewidth=1.5, marker='o')
        for x, y in zip(x_data, y_data):
            label = "{:.2f}".format(y)
            plt.annotate(label,  # this is the text
                         (x, y),  # this is the point to label
                         textcoords="offset points",  # how to position the text
                         xytext=(0, 10),  # distance from text to points (x,y)
                         ha='center')  # horizontal alignment can be left, right or center
        plt.xticks(np.arange(0, 21, 1))
        plt.ylabel('Runtime in s')
        plt.xlabel('Number of segments')
        plt.title("Runtime vs Number of Segments(Signal length = 2.0,Epsilon=0.001)")
        plt.grid()
        plt.show()

    def plot_segment_data(self,x_data,y_data):
        plt.plot(x_data, y_data, 'r', linewidth=1.5, marker='o')
        plt.xticks(x_data)
        for x, y in zip(x_data, y_data):
            label = "{:.2f}".format(y)

            plt.annotate(label,  # this is the text
                         (x, y),  # this is the point to label
                         textcoords="offset points",  # how to position the text
                         xytext=(0, 10),  # distance from text to points (x,y)
                         ha='center')  # horizontal alignment can be left, right or center

        # plt.ylim(-0.2, 0.8)
        plt.ylabel('Runtime in s')
        plt.xlabel('Signal length in s')
        plt.title("Runtime vs Signal length(Epsilon = 0.001")

        plt.grid()
        plt.show()

    def plot_best_segment_data(self,x_data,y_data,best_segment_list):
        plt.plot(x_data, y_data, 'r', linewidth=1.5, marker='o')
        plt.xticks(x_data)

        for x, y, bs in zip(x_data, y_data,best_segment_list):

            label = "{:.2f}".format(y)
            label_best_segment = "{:.2f}".format(bs)
            plt.annotate(label,  # this is the text
                         (x, y),  # this is the point to label
                         textcoords="offset points",  # how to position the text
                         xytext=(0, 10),  # distance from text to points (x,y)
                         ha='center')  # horizontal alignment can be left, right or center
            plt.annotate(label_best_segment,  # this is the text
                         (x, y),  # this is the point to label
                         textcoords="offset points",  # how to position the text
                         xytext=(0, -10),  # distance from text to points (x,y)
                         ha='center')  # horizontal alignment can be left, right or center
        plt.ylabel('Runtime in s')
        plt.xlabel('Signal length in s')
        plt.title("Runtime vs Signal length(Epsilon = 0.001")
        plt.grid()
        plt.show()

    def plot_segment_parts_data(self,x_data,segment_data,segment_parts_data):
        plt.plot(x_data, segment_data, 'r', linewidth=1.5, marker='o',label="1-segment")
        plt.plot(x_data, segment_parts_data, 'b', linewidth=1.5, marker='o',label="N segments")
        plt.ylabel('Runtime in s')
        plt.xlabel('Signal length in s')
        title_txt = "Runtime vs Signal length"+"(Epsilon="+str(self.time_eps)+", N="+str(self.N_parts)+")"
        plt.title(title_txt)
        plt.legend()
        plt.show()


if __name__ == '__main__':
    smt_node = SMTCar()
    if len(sys.argv)<2:
        print("No input arguments detected.Options available: [single, multi]")
        print("e.g. python SMTCar_Multicore.py single")
        exit()
    else:
        arg = sys.argv[1]
        if arg == "single":
            print("executing with Single core")
            smt_node.MULTIPROCESSING_ENABLED= False
        elif arg == "multi":
            print("executing with Multiple cores")
            smt_node.MULTIPROCESSING_ENABLED= True
        else:
            print("Please run program with valid arguments: [single, multi]")
            print("e.g. python SMTCar_Multicore.py single")
            exit()
    smt_node.run_SMT_node()
