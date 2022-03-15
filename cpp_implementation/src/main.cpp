
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include <cmath>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>
#include <vector>
#include <z3++.h>

using namespace z3;

//takes a file name and returns corresponding parsed data vector
std::vector<std::vector<std::string>> getData(std::string fileName)
{
	//data vector
	std::vector<std::vector<std::string>> data;
	
	//input file stream
	std::ifstream file;
	file.open("agent_data/" + fileName);
	
	//string line
	std::string line;
	
	//populate data vector
	if(file.is_open())
	{
		while(!file.eof())
		{
			//get curent line
			getline(file, line);
			
			//input string stream
			std::istringstream iss(line);
			
			//populate value vector (string)
			std::vector<std::string> values((std::istream_iterator<std::string>(iss)), std::istream_iterator<std::string>());
			
			//value vector (double)
			//std::vector<std::string> values;
			
			//cast value vector (string) to value vector (double)
			//for (int i=0; i<values_str.size(); i++) 
		    //{ 
		    //    values.push_back(std::stod(values_str[i]));
		    //}
		    
		    //append data (value vector) to data vector
		    data.push_back(values);
		}
	}
	
	//close file stream
	file.close();
	
	//return data vector
	return data;
}

//takes a data vector and prints its values
void printData(std::vector<std::vector<std::string>> data)
{
	for(int i = 0; i < data.size(); i++) 
    { 
        for(int j = 0; j < data[i].size(); j++) 
	    { 
	        std::cout << data[i][j] << " ";
	    }
	    
	    std::cout << std::endl;
    }
}

//get smt vector based on segments
void runSolver_2(double eps, int segCount, double sigDur, int msgLim)
{
	//enable parallel mode
	//set_param("parallel.enable", true);
	
	//get data
	std::vector<std::vector<std::string>> agentData_0 = getData("agent_0.txt");
	std::vector<std::vector<std::string>> agentData_1 = getData("agent_1.txt");
	
	//safety checks
	if(!(std::stod(agentData_0[0][0]) == 0 && std::stod(agentData_1[0][0]) == 0))
	{
		return;
	}
	
	if(std::stod(agentData_0[1][0]) != std::stod(agentData_1[1][0]))
	{
		return;
	}
	
	//second time-stamp on agent that is to be re-timed
	double t1 = std::stod(agentData_0[1][0]);
	
	//delta
	int delta = 0;
	
	//segment duration
	double segDur = sigDur / segCount;
	
	//check if the segment duration is smaller than the sampling period
	if(segDur < t1)
	{
		segCount = sigDur / t1;
	}
	
	//multiplier for normalization
	double mult = 1 / t1;
	
	//normalization of paramters
	eps *= mult;
	sigDur *= mult;
	segDur *= mult;
	
	//verdict vector
	std::vector<std::string> verdicts;
	
	#pragma omp parallel
	{
		#pragma omp for
		for(int i = 0; i < segCount; i++) 
	    {			
			//segment bounds
			double segLower = (i * segDur) - eps;
			double segUpper = (i + 1) * segDur;
			
		    context c;

		    //solver
		    solver s(c);
		    
		    //co-ord functions
		    func_decl a_0_x = function("a_0_x", c.int_sort(), c.real_sort());
		    func_decl a_0_y = function("a_0_y", c.int_sort(), c.real_sort());
		    func_decl a_0_z = function("a_0_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_1_x = function("a_1_x", c.int_sort(), c.real_sort());
		    func_decl a_1_y = function("a_1_y", c.int_sort(), c.real_sort());
		    func_decl a_1_z = function("a_1_z", c.int_sort(), c.real_sort());
		    
		    //populate co-ord functions
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_0.size())
		        {
		        	s.add(a_0_x(j) == c.real_val(agentData_0[j][1].c_str()));
		        	s.add(a_0_y(j) == c.real_val(agentData_0[j][2].c_str()));
		        	s.add(a_0_z(j) == c.real_val(agentData_0[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_1.size())
		        {
		        	s.add(a_1_x(j) == c.real_val(agentData_1[j][1].c_str()));
		        	s.add(a_1_y(j) == c.real_val(agentData_1[j][2].c_str()));
		        	s.add(a_1_z(j) == c.real_val(agentData_1[j][3].c_str()));
				}
		    }
		    
		    //general smt variables		  
			expr pred_0 = c.int_const("pred_0");
			s.add(pred_0 >= (int)segLower + 1 && pred_0 <= (int)segUpper);
			
		    expr pred_1 = c.int_const("pred_1");
		    s.add(pred_1 >= (int)segLower + 1 && pred_1 <= (int)segUpper);
		    
		    // =============== AGENT 0 AND AGENT 1 START =============== //
			
			//agent pair smt variables
			expr t_01 = c.int_const("t_01");
		    s.add(t_01 >= (int)segLower + 1 && t_01 <= (int)segUpper);
		    
		    expr t_before_01 = c.int_const("t_before_01");
		    expr t_after_01 = c.int_const("t_after_01");
		    s.add(t_before_01 >= (int)segLower + 1 && t_before_01 <= (int)segUpper && t_after_01 >= (int)segLower && t_after_01 <= (int)segUpper);
		    
		    func_decl rho_01 = function("rho_01", c.int_sort(), c.int_sort());
		    func_decl rho_primed_01 = function("rho_primed_01", c.real_sort(), c.real_sort());
		    
		    func_decl rho_10 = function("rho_10", c.int_sort(), c.int_sort());
		    func_decl rho_primed_10 = function("rho_primed_10", c.real_sort(), c.real_sort());
		    
		    expr pwl_01 = c.int_const("pwl_01");
		    s.add(pwl_01 >= (int)segLower + 1 && pwl_01 <= (int)segUpper);
		    
		    expr pwl_10 = c.int_const("pwl_10");
		    s.add(pwl_10 >= (int)segLower + 1 && pwl_10 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_01, t_after_01, implies(((t_before_01 < t_after_01) && (t_before_01 >= (int)segLower + 1) && (t_before_01 <= (int)segUpper) && (t_after_01 >= (int)segLower) && (t_after_01 <= (int)segUpper)), ((rho_01(t_before_01) < rho_01(t_after_01)) && (rho_10(t_before_01) < rho_10(t_after_01))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_1, implies(((rho_01(pred_0) == pred_1) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_1 >= (int)segLower) && (pred_1 <= (int)segUpper)), (c.real_val(delta) <= (((a_1_x(pred_1) - a_0_x(pred_0)) * (a_1_x(pred_1) - a_0_x(pred_0))) + ((a_1_y(pred_1) - a_0_y(pred_0)) * (a_1_y(pred_1) - a_0_y(pred_0))) + ((a_1_z(pred_1) - a_0_z(pred_0)) * (a_1_z(pred_1) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_01, implies(((pwl_01 >= (int)segLower + 1) && (pwl_01 <= (int)segUpper)), (rho_primed_01(pwl_01) == rho_01(c.int_val(pwl_01)) + ((pwl_01 - c.int_val(pwl_01)) * (rho_01(c.int_val(pwl_01) + 1) - rho_01(c.int_val(pwl_01))))))));
			s.add(forall(pwl_10, implies(((pwl_10 >= (int)segLower + 1) && (pwl_10 <= (int)segUpper)), (rho_primed_10(pwl_10) == rho_10(c.int_val(pwl_10)) + ((pwl_10 - c.int_val(pwl_10)) * (rho_10(c.int_val(pwl_10) + 1) - rho_10(c.int_val(pwl_10))))))));
			
			//inverse re-timing
			s.add(forall(t_01, implies(((t_01 >= (int)segLower) && (t_01 <= (int)segUpper)), (rho_10(rho_01(t_01)) == t_01))));

			// ================ AGENT 0 AND AGENT 1 END ================ //
			
			if(s.check() == sat)
		    {
		    	std::string verdict = std::to_string(i) + " : Sat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    else
		    {
		    	std::string verdict = std::to_string(i) + " : Unsat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    
		    //reset solver
		    //s.reset();
		    
		    //build and show model
		    //model m = s.get_model();
    		//std::cout << m << "\n";
	    }
	}
	//return verdicts;
}

void runSolver_3(double eps, int segCount, double sigDur, int msgLim)
{
	//enable parallel mode
	//set_param("parallel.enable", true);
	
	//get data
	std::vector<std::vector<std::string>> agentData_0 = getData("agent_0.txt");
	std::vector<std::vector<std::string>> agentData_1 = getData("agent_1.txt");
	std::vector<std::vector<std::string>> agentData_2 = getData("agent_2.txt");
	
	//safety checks
	if(!(std::stod(agentData_0[0][0]) == 0 && std::stod(agentData_1[0][0]) == 0))
	{
		return;
	}
	
	if(std::stod(agentData_0[1][0]) != std::stod(agentData_1[1][0]))
	{
		return;
	}
	
	//second time-stamp on agent that is to be re-timed
	double t1 = std::stod(agentData_0[1][0]);
	
	//delta
	int delta = 0;
	
	//segment duration
	double segDur = sigDur / segCount;
	
	//check if the segment duration is smaller than the sampling period
	if(segDur < t1)
	{
		segCount = sigDur / t1;
	}
	
	//multiplier for normalization
	double mult = 1 / t1;
	
	//normalization of paramters
	eps *= mult;
	sigDur *= mult;
	segDur *= mult;
	
	//verdict vector
	std::vector<std::string> verdicts;
	
	#pragma omp parallel
	{
		#pragma omp for
		for(int i = 0; i < segCount; i++) 
	    {			
			//segment bounds
			double segLower = (i * segDur) - eps;
			double segUpper = (i + 1) * segDur;
			
		    context c;

		    //solver
		    solver s(c);
		    
		    //co-ord functions
		    func_decl a_0_x = function("a_0_x", c.int_sort(), c.real_sort());
		    func_decl a_0_y = function("a_0_y", c.int_sort(), c.real_sort());
		    func_decl a_0_z = function("a_0_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_1_x = function("a_1_x", c.int_sort(), c.real_sort());
		    func_decl a_1_y = function("a_1_y", c.int_sort(), c.real_sort());
		    func_decl a_1_z = function("a_1_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_2_x = function("a_2_x", c.int_sort(), c.real_sort());
		    func_decl a_2_y = function("a_2_y", c.int_sort(), c.real_sort());
		    func_decl a_2_z = function("a_2_z", c.int_sort(), c.real_sort());
		    
		    //populate co-ord functions
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_0.size())
		        {
		        	s.add(a_0_x(j) == c.real_val(agentData_0[j][1].c_str()));
		        	s.add(a_0_y(j) == c.real_val(agentData_0[j][2].c_str()));
		        	s.add(a_0_z(j) == c.real_val(agentData_0[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_1.size())
		        {
		        	s.add(a_1_x(j) == c.real_val(agentData_1[j][1].c_str()));
		        	s.add(a_1_y(j) == c.real_val(agentData_1[j][2].c_str()));
		        	s.add(a_1_z(j) == c.real_val(agentData_1[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_2.size())
		        {
		        	s.add(a_2_x(j) == c.real_val(agentData_2[j][1].c_str()));
		        	s.add(a_2_y(j) == c.real_val(agentData_2[j][2].c_str()));
		        	s.add(a_2_z(j) == c.real_val(agentData_2[j][3].c_str()));
				}
		    }
		    
		    //general smt variables		  
			expr pred_0 = c.int_const("pred_0");
			s.add(pred_0 >= (int)segLower + 1 && pred_0 <= (int)segUpper);
			
		    expr pred_1 = c.int_const("pred_1");
		    s.add(pred_1 >= (int)segLower + 1 && pred_1 <= (int)segUpper);
		    
		    expr pred_2 = c.int_const("pred_2");
		    s.add(pred_2 >= (int)segLower + 1 && pred_2 <= (int)segUpper);
		    
		    // =============== AGENT 0 AND AGENT 1 START =============== //
			
			//agent pair smt variables
			expr t_01 = c.int_const("t_01");
		    s.add(t_01 >= (int)segLower + 1 && t_01 <= (int)segUpper);
		    
		    expr t_before_01 = c.int_const("t_before_01");
		    expr t_after_01 = c.int_const("t_after_01");
		    s.add(t_before_01 >= (int)segLower + 1 && t_before_01 <= (int)segUpper && t_after_01 >= (int)segLower && t_after_01 <= (int)segUpper);
		    
		    func_decl rho_01 = function("rho_01", c.int_sort(), c.int_sort());
		    func_decl rho_primed_01 = function("rho_primed_01", c.real_sort(), c.real_sort());
		    
		    func_decl rho_10 = function("rho_10", c.int_sort(), c.int_sort());
		    func_decl rho_primed_10 = function("rho_primed_10", c.real_sort(), c.real_sort());
		    
		    expr pwl_01 = c.int_const("pwl_01");
		    s.add(pwl_01 >= (int)segLower + 1 && pwl_01 <= (int)segUpper);
		    
		    expr pwl_10 = c.int_const("pwl_10");
		    s.add(pwl_10 >= (int)segLower + 1 && pwl_10 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_01, t_after_01, implies(((t_before_01 < t_after_01) && (t_before_01 >= (int)segLower + 1) && (t_before_01 <= (int)segUpper) && (t_after_01 >= (int)segLower) && (t_after_01 <= (int)segUpper)), ((rho_01(t_before_01) < rho_01(t_after_01)) && (rho_10(t_before_01) < rho_10(t_after_01))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_1, implies(((rho_01(pred_0) == pred_1) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_1 >= (int)segLower) && (pred_1 <= (int)segUpper)), (c.real_val(delta) <= (((a_1_x(pred_1) - a_0_x(pred_0)) * (a_1_x(pred_1) - a_0_x(pred_0))) + ((a_1_y(pred_1) - a_0_y(pred_0)) * (a_1_y(pred_1) - a_0_y(pred_0))) + ((a_1_z(pred_1) - a_0_z(pred_0)) * (a_1_z(pred_1) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_01, implies(((pwl_01 >= (int)segLower + 1) && (pwl_01 <= (int)segUpper)), (rho_primed_01(pwl_01) == rho_01(c.int_val(pwl_01)) + ((pwl_01 - c.int_val(pwl_01)) * (rho_01(c.int_val(pwl_01) + 1) - rho_01(c.int_val(pwl_01))))))));
			s.add(forall(pwl_10, implies(((pwl_10 >= (int)segLower + 1) && (pwl_10 <= (int)segUpper)), (rho_primed_10(pwl_10) == rho_10(c.int_val(pwl_10)) + ((pwl_10 - c.int_val(pwl_10)) * (rho_10(c.int_val(pwl_10) + 1) - rho_10(c.int_val(pwl_10))))))));
			
			//inverse re-timing
			s.add(forall(t_01, implies(((t_01 >= (int)segLower) && (t_01 <= (int)segUpper)), (rho_10(rho_01(t_01)) == t_01))));

			// ================ AGENT 0 AND AGENT 1 END ================ //
			
			// =============== AGENT 0 AND AGENT 2 START =============== //
			
			//agent pair smt variables
			expr t_02 = c.int_const("t_02");
		    s.add(t_02 >= (int)segLower + 1 && t_02 <= (int)segUpper);
		    
		    expr t_before_02 = c.int_const("t_before_02");
		    expr t_after_02 = c.int_const("t_after_02");
		    s.add(t_before_02 >= (int)segLower + 1 && t_before_02 <= (int)segUpper && t_after_02 >= (int)segLower && t_after_02 <= (int)segUpper);
		    
		    func_decl rho_02 = function("rho_02", c.int_sort(), c.int_sort());
		    func_decl rho_primed_02 = function("rho_primed_02", c.real_sort(), c.real_sort());
		    
		    func_decl rho_20 = function("rho_20", c.int_sort(), c.int_sort());
		    func_decl rho_primed_20 = function("rho_primed_20", c.real_sort(), c.real_sort());
		    
		    expr pwl_02 = c.int_const("pwl_02");
		    s.add(pwl_02 >= (int)segLower + 1 && pwl_02 <= (int)segUpper);
		    
		    expr pwl_20 = c.int_const("pwl_20");
		    s.add(pwl_20 >= (int)segLower + 1 && pwl_20 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_02(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_02(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_20(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_20(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_02, t_after_02, implies(((t_before_02 < t_after_02) && (t_before_02 >= (int)segLower + 1) && (t_before_02 <= (int)segUpper) && (t_after_02 >= (int)segLower) && (t_after_02 <= (int)segUpper)), ((rho_02(t_before_02) < rho_02(t_after_02)) && (rho_20(t_before_02) < rho_20(t_after_02))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_2, implies(((rho_02(pred_0) == pred_2) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_2 >= (int)segLower) && (pred_2 <= (int)segUpper)), (c.real_val(delta) <= (((a_2_x(pred_2) - a_0_x(pred_0)) * (a_2_x(pred_2) - a_0_x(pred_0))) + ((a_2_y(pred_2) - a_0_y(pred_0)) * (a_2_y(pred_2) - a_0_y(pred_0))) + ((a_2_z(pred_2) - a_0_z(pred_0)) * (a_2_z(pred_2) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_02, implies(((pwl_02 >= (int)segLower + 1) && (pwl_02 <= (int)segUpper)), (rho_primed_02(pwl_02) == rho_02(c.int_val(pwl_02)) + ((pwl_02 - c.int_val(pwl_02)) * (rho_02(c.int_val(pwl_02) + 1) - rho_02(c.int_val(pwl_02))))))));
			s.add(forall(pwl_20, implies(((pwl_20 >= (int)segLower + 1) && (pwl_20 <= (int)segUpper)), (rho_primed_20(pwl_20) == rho_20(c.int_val(pwl_20)) + ((pwl_20 - c.int_val(pwl_20)) * (rho_20(c.int_val(pwl_20) + 1) - rho_20(c.int_val(pwl_20))))))));
			
			//inverse re-timing
			s.add(forall(t_02, implies(((t_02 >= (int)segLower) && (t_02 <= (int)segUpper)), (rho_20(rho_02(t_02)) == t_02))));

			// ================ AGENT 0 AND AGENT 2 END ================ //
			
			// =============== AGENT 1 AND AGENT 2 START =============== //
			
			//agent pair smt variables
			expr t_12 = c.int_const("t_12");
		    s.add(t_12 >= (int)segLower + 1 && t_12 <= (int)segUpper);
		    
		    expr t_before_12 = c.int_const("t_before_12");
		    expr t_after_12 = c.int_const("t_after_12");
		    s.add(t_before_12 >= (int)segLower + 1 && t_before_12 <= (int)segUpper && t_after_12 >= (int)segLower && t_after_12 <= (int)segUpper);
		    
		    func_decl rho_12 = function("rho_12", c.int_sort(), c.int_sort());
		    func_decl rho_primed_12 = function("rho_primed_12", c.real_sort(), c.real_sort());
		    
		    func_decl rho_21 = function("rho_21", c.int_sort(), c.int_sort());
		    func_decl rho_primed_21 = function("rho_primed_21", c.real_sort(), c.real_sort());
		    
		    expr pwl_12 = c.int_const("pwl_12");
		    s.add(pwl_12 >= (int)segLower + 1 && pwl_12 <= (int)segUpper);
		    
		    expr pwl_21 = c.int_const("pwl_21");
		    s.add(pwl_21 >= (int)segLower + 1 && pwl_21 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_12(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_12(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_21(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_21(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_12, t_after_12, implies(((t_before_12 < t_after_12) && (t_before_12 >= (int)segLower + 1) && (t_before_12 <= (int)segUpper) && (t_after_12 >= (int)segLower) && (t_after_12 <= (int)segUpper)), ((rho_12(t_before_12) < rho_12(t_after_12)) && (rho_21(t_before_12) < rho_21(t_after_12))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_2, implies(((rho_12(pred_1) == pred_2) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_2 >= (int)segLower) && (pred_2 <= (int)segUpper)), (c.real_val(delta) <= (((a_2_x(pred_2) - a_0_x(pred_1)) * (a_2_x(pred_2) - a_0_x(pred_1))) + ((a_2_y(pred_2) - a_0_y(pred_1)) * (a_2_y(pred_2) - a_0_y(pred_1))) + ((a_2_z(pred_2) - a_0_z(pred_1)) * (a_2_z(pred_2) - a_0_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_12, implies(((pwl_12 >= (int)segLower + 1) && (pwl_12 <= (int)segUpper)), (rho_primed_12(pwl_12) == rho_12(c.int_val(pwl_12)) + ((pwl_12 - c.int_val(pwl_12)) * (rho_12(c.int_val(pwl_12) + 1) - rho_12(c.int_val(pwl_12))))))));
			s.add(forall(pwl_21, implies(((pwl_21 >= (int)segLower + 1) && (pwl_21 <= (int)segUpper)), (rho_primed_21(pwl_21) == rho_21(c.int_val(pwl_21)) + ((pwl_21 - c.int_val(pwl_21)) * (rho_21(c.int_val(pwl_21) + 1) - rho_21(c.int_val(pwl_21))))))));
			
			//inverse re-timing
			s.add(forall(t_12, implies(((t_12 >= (int)segLower) && (t_12 <= (int)segUpper)), (rho_21(rho_12(t_12)) == t_12))));

			// ================ AGENT 1 AND AGENT 2 END ================ //
			
			if(s.check() == sat)
		    {
		    	std::string verdict = std::to_string(i) + " : Sat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    else
		    {
		    	std::string verdict = std::to_string(i) + " : Unsat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    
		    //reset solver
		    //s.reset();
		    
		    //build and show model
		    //model m = s.get_model();
    		//std::cout << m << "\n";
	    }
	}
	//return verdicts;
}

void runSolver_4(double eps, int segCount, double sigDur, int msgLim)
{
	//enable parallel mode
	//set_param("parallel.enable", true);
	
	//get data
	std::vector<std::vector<std::string>> agentData_0 = getData("agent_0.txt");
	std::vector<std::vector<std::string>> agentData_1 = getData("agent_1.txt");
	std::vector<std::vector<std::string>> agentData_2 = getData("agent_2.txt");
	std::vector<std::vector<std::string>> agentData_3 = getData("agent_3.txt");
	
	
	//safety checks
	if(!(std::stod(agentData_0[0][0]) == 0 && std::stod(agentData_1[0][0]) == 0))
	{
		return;
	}
	
	if(std::stod(agentData_0[1][0]) != std::stod(agentData_1[1][0]))
	{
		return;
	}
	
	//second time-stamp on agent that is to be re-timed
	double t1 = std::stod(agentData_0[1][0]);
	
	//delta
	int delta = 0;
	
	//segment duration
	double segDur = sigDur / segCount;
	
	//check if the segment duration is smaller than the sampling period
	if(segDur < t1)
	{
		segCount = sigDur / t1;
	}
	
	//multiplier for normalization
	double mult = 1 / t1;
	
	//normalization of paramters
	eps *= mult;
	sigDur *= mult;
	segDur *= mult;
	
	//verdict vector
	std::vector<std::string> verdicts;
	
	#pragma omp parallel
	{
		#pragma omp for
		for(int i = 0; i < segCount; i++) 
	    {			
			//segment bounds
			double segLower = (i * segDur) - eps;
			double segUpper = (i + 1) * segDur;
			
		    context c;

		    //solver
		    solver s(c);
		    
		    //co-ord functions
		    func_decl a_0_x = function("a_0_x", c.int_sort(), c.real_sort());
		    func_decl a_0_y = function("a_0_y", c.int_sort(), c.real_sort());
		    func_decl a_0_z = function("a_0_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_1_x = function("a_1_x", c.int_sort(), c.real_sort());
		    func_decl a_1_y = function("a_1_y", c.int_sort(), c.real_sort());
		    func_decl a_1_z = function("a_1_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_2_x = function("a_2_x", c.int_sort(), c.real_sort());
		    func_decl a_2_y = function("a_2_y", c.int_sort(), c.real_sort());
		    func_decl a_2_z = function("a_2_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_3_x = function("a_3_x", c.int_sort(), c.real_sort());
		    func_decl a_3_y = function("a_3_y", c.int_sort(), c.real_sort());
		    func_decl a_3_z = function("a_3_z", c.int_sort(), c.real_sort());
		    
		    //populate co-ord functions
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_0.size())
		        {
		        	s.add(a_0_x(j) == c.real_val(agentData_0[j][1].c_str()));
		        	s.add(a_0_y(j) == c.real_val(agentData_0[j][2].c_str()));
		        	s.add(a_0_z(j) == c.real_val(agentData_0[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_1.size())
		        {
		        	s.add(a_1_x(j) == c.real_val(agentData_1[j][1].c_str()));
		        	s.add(a_1_y(j) == c.real_val(agentData_1[j][2].c_str()));
		        	s.add(a_1_z(j) == c.real_val(agentData_1[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_2.size())
		        {
		        	s.add(a_2_x(j) == c.real_val(agentData_2[j][1].c_str()));
		        	s.add(a_2_y(j) == c.real_val(agentData_2[j][2].c_str()));
		        	s.add(a_2_z(j) == c.real_val(agentData_2[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_3.size())
		        {
		        	s.add(a_3_x(j) == c.real_val(agentData_3[j][1].c_str()));
		        	s.add(a_3_y(j) == c.real_val(agentData_3[j][2].c_str()));
		        	s.add(a_3_z(j) == c.real_val(agentData_3[j][3].c_str()));
				}
		    }
		    
		    //general smt variables		  
			expr pred_0 = c.int_const("pred_0");
			s.add(pred_0 >= (int)segLower + 1 && pred_0 <= (int)segUpper);
			
		    expr pred_1 = c.int_const("pred_1");
		    s.add(pred_1 >= (int)segLower + 1 && pred_1 <= (int)segUpper);
		    
		    expr pred_2 = c.int_const("pred_2");
		    s.add(pred_2 >= (int)segLower + 1 && pred_2 <= (int)segUpper);
		    
		    expr pred_3 = c.int_const("pred_3");
		    s.add(pred_3 >= (int)segLower + 1 && pred_3 <= (int)segUpper);
		    
		    // =============== AGENT 0 AND AGENT 1 START =============== //
			
			//agent pair smt variables
			expr t_01 = c.int_const("t_01");
		    s.add(t_01 >= (int)segLower + 1 && t_01 <= (int)segUpper);
		    
		    expr t_before_01 = c.int_const("t_before_01");
		    expr t_after_01 = c.int_const("t_after_01");
		    s.add(t_before_01 >= (int)segLower + 1 && t_before_01 <= (int)segUpper && t_after_01 >= (int)segLower && t_after_01 <= (int)segUpper);
		    
		    func_decl rho_01 = function("rho_01", c.int_sort(), c.int_sort());
		    func_decl rho_primed_01 = function("rho_primed_01", c.real_sort(), c.real_sort());
		    
		    func_decl rho_10 = function("rho_10", c.int_sort(), c.int_sort());
		    func_decl rho_primed_10 = function("rho_primed_10", c.real_sort(), c.real_sort());
		    
		    expr pwl_01 = c.int_const("pwl_01");
		    s.add(pwl_01 >= (int)segLower + 1 && pwl_01 <= (int)segUpper);
		    
		    expr pwl_10 = c.int_const("pwl_10");
		    s.add(pwl_10 >= (int)segLower + 1 && pwl_10 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_01, t_after_01, implies(((t_before_01 < t_after_01) && (t_before_01 >= (int)segLower + 1) && (t_before_01 <= (int)segUpper) && (t_after_01 >= (int)segLower) && (t_after_01 <= (int)segUpper)), ((rho_01(t_before_01) < rho_01(t_after_01)) && (rho_10(t_before_01) < rho_10(t_after_01))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_1, implies(((rho_01(pred_0) == pred_1) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_1 >= (int)segLower) && (pred_1 <= (int)segUpper)), (c.real_val(delta) <= (((a_1_x(pred_1) - a_0_x(pred_0)) * (a_1_x(pred_1) - a_0_x(pred_0))) + ((a_1_y(pred_1) - a_0_y(pred_0)) * (a_1_y(pred_1) - a_0_y(pred_0))) + ((a_1_z(pred_1) - a_0_z(pred_0)) * (a_1_z(pred_1) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_01, implies(((pwl_01 >= (int)segLower + 1) && (pwl_01 <= (int)segUpper)), (rho_primed_01(pwl_01) == rho_01(c.int_val(pwl_01)) + ((pwl_01 - c.int_val(pwl_01)) * (rho_01(c.int_val(pwl_01) + 1) - rho_01(c.int_val(pwl_01))))))));
			s.add(forall(pwl_10, implies(((pwl_10 >= (int)segLower + 1) && (pwl_10 <= (int)segUpper)), (rho_primed_10(pwl_10) == rho_10(c.int_val(pwl_10)) + ((pwl_10 - c.int_val(pwl_10)) * (rho_10(c.int_val(pwl_10) + 1) - rho_10(c.int_val(pwl_10))))))));
			
			//inverse re-timing
			s.add(forall(t_01, implies(((t_01 >= (int)segLower) && (t_01 <= (int)segUpper)), (rho_10(rho_01(t_01)) == t_01))));

			// ================ AGENT 0 AND AGENT 1 END ================ //
			
			// =============== AGENT 0 AND AGENT 2 START =============== //
			
			//agent pair smt variables
			expr t_02 = c.int_const("t_02");
		    s.add(t_02 >= (int)segLower + 1 && t_02 <= (int)segUpper);
		    
		    expr t_before_02 = c.int_const("t_before_02");
		    expr t_after_02 = c.int_const("t_after_02");
		    s.add(t_before_02 >= (int)segLower + 1 && t_before_02 <= (int)segUpper && t_after_02 >= (int)segLower && t_after_02 <= (int)segUpper);
		    
		    func_decl rho_02 = function("rho_02", c.int_sort(), c.int_sort());
		    func_decl rho_primed_02 = function("rho_primed_02", c.real_sort(), c.real_sort());
		    
		    func_decl rho_20 = function("rho_20", c.int_sort(), c.int_sort());
		    func_decl rho_primed_20 = function("rho_primed_20", c.real_sort(), c.real_sort());
		    
		    expr pwl_02 = c.int_const("pwl_02");
		    s.add(pwl_02 >= (int)segLower + 1 && pwl_02 <= (int)segUpper);
		    
		    expr pwl_20 = c.int_const("pwl_20");
		    s.add(pwl_20 >= (int)segLower + 1 && pwl_20 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_02(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_02(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_20(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_20(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_02, t_after_02, implies(((t_before_02 < t_after_02) && (t_before_02 >= (int)segLower + 1) && (t_before_02 <= (int)segUpper) && (t_after_02 >= (int)segLower) && (t_after_02 <= (int)segUpper)), ((rho_02(t_before_02) < rho_02(t_after_02)) && (rho_20(t_before_02) < rho_20(t_after_02))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_2, implies(((rho_02(pred_0) == pred_2) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_2 >= (int)segLower) && (pred_2 <= (int)segUpper)), (c.real_val(delta) <= (((a_2_x(pred_2) - a_0_x(pred_0)) * (a_2_x(pred_2) - a_0_x(pred_0))) + ((a_2_y(pred_2) - a_0_y(pred_0)) * (a_2_y(pred_2) - a_0_y(pred_0))) + ((a_2_z(pred_2) - a_0_z(pred_0)) * (a_2_z(pred_2) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_02, implies(((pwl_02 >= (int)segLower + 1) && (pwl_02 <= (int)segUpper)), (rho_primed_02(pwl_02) == rho_02(c.int_val(pwl_02)) + ((pwl_02 - c.int_val(pwl_02)) * (rho_02(c.int_val(pwl_02) + 1) - rho_02(c.int_val(pwl_02))))))));
			s.add(forall(pwl_20, implies(((pwl_20 >= (int)segLower + 1) && (pwl_20 <= (int)segUpper)), (rho_primed_20(pwl_20) == rho_20(c.int_val(pwl_20)) + ((pwl_20 - c.int_val(pwl_20)) * (rho_20(c.int_val(pwl_20) + 1) - rho_20(c.int_val(pwl_20))))))));
			
			//inverse re-timing
			s.add(forall(t_02, implies(((t_02 >= (int)segLower) && (t_02 <= (int)segUpper)), (rho_20(rho_02(t_02)) == t_02))));

			// ================ AGENT 0 AND AGENT 2 END ================ //
			
			// =============== AGENT 0 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_03 = c.int_const("t_03");
		    s.add(t_03 >= (int)segLower + 1 && t_03 <= (int)segUpper);
		    
		    expr t_before_03 = c.int_const("t_before_03");
		    expr t_after_03 = c.int_const("t_after_03");
		    s.add(t_before_03 >= (int)segLower + 1 && t_before_03 <= (int)segUpper && t_after_03 >= (int)segLower && t_after_03 <= (int)segUpper);
		    
		    func_decl rho_03 = function("rho_03", c.int_sort(), c.int_sort());
		    func_decl rho_primed_03 = function("rho_primed_03", c.real_sort(), c.real_sort());
		    
		    func_decl rho_30 = function("rho_30", c.int_sort(), c.int_sort());
		    func_decl rho_primed_30 = function("rho_primed_30", c.real_sort(), c.real_sort());
		    
		    expr pwl_03 = c.int_const("pwl_03");
		    s.add(pwl_03 >= (int)segLower + 1 && pwl_03 <= (int)segUpper);
		    
		    expr pwl_30 = c.int_const("pwl_30");
		    s.add(pwl_30 >= (int)segLower + 1 && pwl_30 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_03(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_03(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_30(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_30(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_03, t_after_03, implies(((t_before_03 < t_after_03) && (t_before_03 >= (int)segLower + 1) && (t_before_03 <= (int)segUpper) && (t_after_03 >= (int)segLower) && (t_after_03 <= (int)segUpper)), ((rho_03(t_before_03) < rho_03(t_after_03)) && (rho_30(t_before_03) < rho_30(t_after_03))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_3, implies(((rho_03(pred_0) == pred_3) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_0_x(pred_0)) * (a_3_x(pred_3) - a_0_x(pred_0))) + ((a_3_y(pred_3) - a_0_y(pred_0)) * (a_3_y(pred_3) - a_0_y(pred_0))) + ((a_3_z(pred_3) - a_0_z(pred_0)) * (a_3_z(pred_3) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_03, implies(((pwl_03 >= (int)segLower + 1) && (pwl_03 <= (int)segUpper)), (rho_primed_03(pwl_03) == rho_03(c.int_val(pwl_03)) + ((pwl_03 - c.int_val(pwl_03)) * (rho_03(c.int_val(pwl_03) + 1) - rho_03(c.int_val(pwl_03))))))));
			s.add(forall(pwl_30, implies(((pwl_30 >= (int)segLower + 1) && (pwl_30 <= (int)segUpper)), (rho_primed_30(pwl_30) == rho_30(c.int_val(pwl_30)) + ((pwl_30 - c.int_val(pwl_30)) * (rho_30(c.int_val(pwl_30) + 1) - rho_30(c.int_val(pwl_30))))))));
			
			//inverse re-timing
			s.add(forall(t_03, implies(((t_03 >= (int)segLower) && (t_03 <= (int)segUpper)), (rho_30(rho_03(t_03)) == t_03))));

			// ================ AGENT 0 AND AGENT 3 END ================ //
			
			// =============== AGENT 1 AND AGENT 2 START =============== //
			
			//agent pair smt variables
			expr t_12 = c.int_const("t_12");
		    s.add(t_12 >= (int)segLower + 1 && t_12 <= (int)segUpper);
		    
		    expr t_before_12 = c.int_const("t_before_12");
		    expr t_after_12 = c.int_const("t_after_12");
		    s.add(t_before_12 >= (int)segLower + 1 && t_before_12 <= (int)segUpper && t_after_12 >= (int)segLower && t_after_12 <= (int)segUpper);
		    
		    func_decl rho_12 = function("rho_12", c.int_sort(), c.int_sort());
		    func_decl rho_primed_12 = function("rho_primed_12", c.real_sort(), c.real_sort());
		    
		    func_decl rho_21 = function("rho_21", c.int_sort(), c.int_sort());
		    func_decl rho_primed_21 = function("rho_primed_21", c.real_sort(), c.real_sort());
		    
		    expr pwl_12 = c.int_const("pwl_12");
		    s.add(pwl_12 >= (int)segLower + 1 && pwl_12 <= (int)segUpper);
		    
		    expr pwl_21 = c.int_const("pwl_21");
		    s.add(pwl_21 >= (int)segLower + 1 && pwl_21 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_12(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_12(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_21(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_21(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_12, t_after_12, implies(((t_before_12 < t_after_12) && (t_before_12 >= (int)segLower + 1) && (t_before_12 <= (int)segUpper) && (t_after_12 >= (int)segLower) && (t_after_12 <= (int)segUpper)), ((rho_12(t_before_12) < rho_12(t_after_12)) && (rho_21(t_before_12) < rho_21(t_after_12))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_2, implies(((rho_12(pred_1) == pred_2) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_2 >= (int)segLower) && (pred_2 <= (int)segUpper)), (c.real_val(delta) <= (((a_2_x(pred_2) - a_1_x(pred_1)) * (a_2_x(pred_2) - a_1_x(pred_1))) + ((a_2_y(pred_2) - a_1_y(pred_1)) * (a_2_y(pred_2) - a_1_y(pred_1))) + ((a_2_z(pred_2) - a_1_z(pred_1)) * (a_2_z(pred_2) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_12, implies(((pwl_12 >= (int)segLower + 1) && (pwl_12 <= (int)segUpper)), (rho_primed_12(pwl_12) == rho_12(c.int_val(pwl_12)) + ((pwl_12 - c.int_val(pwl_12)) * (rho_12(c.int_val(pwl_12) + 1) - rho_12(c.int_val(pwl_12))))))));
			s.add(forall(pwl_21, implies(((pwl_21 >= (int)segLower + 1) && (pwl_21 <= (int)segUpper)), (rho_primed_21(pwl_21) == rho_21(c.int_val(pwl_21)) + ((pwl_21 - c.int_val(pwl_21)) * (rho_21(c.int_val(pwl_21) + 1) - rho_21(c.int_val(pwl_21))))))));
			
			//inverse re-timing
			s.add(forall(t_12, implies(((t_12 >= (int)segLower) && (t_12 <= (int)segUpper)), (rho_21(rho_12(t_12)) == t_12))));

			// ================ AGENT 1 AND AGENT 2 END ================ //
			
			// =============== AGENT 1 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_13 = c.int_const("t_13");
		    s.add(t_13 >= (int)segLower + 1 && t_13 <= (int)segUpper);
		    
		    expr t_before_13 = c.int_const("t_before_13");
		    expr t_after_13 = c.int_const("t_after_13");
		    s.add(t_before_13 >= (int)segLower + 1 && t_before_13 <= (int)segUpper && t_after_13 >= (int)segLower && t_after_13 <= (int)segUpper);
		    
		    func_decl rho_13 = function("rho_13", c.int_sort(), c.int_sort());
		    func_decl rho_primed_13 = function("rho_primed_13", c.real_sort(), c.real_sort());
		    
		    func_decl rho_31 = function("rho_31", c.int_sort(), c.int_sort());
		    func_decl rho_primed_31 = function("rho_primed_31", c.real_sort(), c.real_sort());
		    
		    expr pwl_13 = c.int_const("pwl_13");
		    s.add(pwl_13 >= (int)segLower + 1 && pwl_13 <= (int)segUpper);
		    
		    expr pwl_31 = c.int_const("pwl_31");
		    s.add(pwl_31 >= (int)segLower + 1 && pwl_31 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_13(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_13(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_31(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_31(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_13, t_after_13, implies(((t_before_13 < t_after_13) && (t_before_13 >= (int)segLower + 1) && (t_before_13 <= (int)segUpper) && (t_after_13 >= (int)segLower) && (t_after_13 <= (int)segUpper)), ((rho_13(t_before_13) < rho_13(t_after_13)) && (rho_31(t_before_13) < rho_31(t_after_13))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_3, implies(((rho_13(pred_1) == pred_3) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_1_x(pred_1)) * (a_3_x(pred_3) - a_1_x(pred_1))) + ((a_3_y(pred_3) - a_1_y(pred_1)) * (a_3_y(pred_3) - a_1_y(pred_1))) + ((a_3_z(pred_3) - a_1_z(pred_1)) * (a_3_z(pred_3) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_13, implies(((pwl_13 >= (int)segLower + 1) && (pwl_13 <= (int)segUpper)), (rho_primed_13(pwl_13) == rho_13(c.int_val(pwl_13)) + ((pwl_13 - c.int_val(pwl_13)) * (rho_13(c.int_val(pwl_13) + 1) - rho_13(c.int_val(pwl_13))))))));
			s.add(forall(pwl_31, implies(((pwl_31 >= (int)segLower + 1) && (pwl_31 <= (int)segUpper)), (rho_primed_31(pwl_31) == rho_31(c.int_val(pwl_31)) + ((pwl_31 - c.int_val(pwl_31)) * (rho_31(c.int_val(pwl_31) + 1) - rho_31(c.int_val(pwl_31))))))));
			
			//inverse re-timing
			s.add(forall(t_13, implies(((t_13 >= (int)segLower) && (t_13 <= (int)segUpper)), (rho_31(rho_13(t_13)) == t_13))));

			// ================ AGENT 1 AND AGENT 3 END ================ //
			
			// =============== AGENT 2 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_23 = c.int_const("t_23");
		    s.add(t_23 >= (int)segLower + 1 && t_23 <= (int)segUpper);
		    
		    expr t_before_23 = c.int_const("t_before_23");
		    expr t_after_23 = c.int_const("t_after_23");
		    s.add(t_before_23 >= (int)segLower + 1 && t_before_23 <= (int)segUpper && t_after_23 >= (int)segLower && t_after_23 <= (int)segUpper);
		    
		    func_decl rho_23 = function("rho_23", c.int_sort(), c.int_sort());
		    func_decl rho_primed_23 = function("rho_primed_23", c.real_sort(), c.real_sort());
		    
		    func_decl rho_32 = function("rho_32", c.int_sort(), c.int_sort());
		    func_decl rho_primed_32 = function("rho_primed_32", c.real_sort(), c.real_sort());
		    
		    expr pwl_23 = c.int_const("pwl_23");
		    s.add(pwl_23 >= (int)segLower + 1 && pwl_23 <= (int)segUpper);
		    
		    expr pwl_32 = c.int_const("pwl_32");
		    s.add(pwl_32 >= (int)segLower + 1 && pwl_32 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_23(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_23(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_32(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_32(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_23, t_after_23, implies(((t_before_23 < t_after_23) && (t_before_23 >= (int)segLower + 1) && (t_before_23 <= (int)segUpper) && (t_after_23 >= (int)segLower) && (t_after_23 <= (int)segUpper)), ((rho_23(t_before_23) < rho_23(t_after_23)) && (rho_32(t_before_23) < rho_32(t_after_23))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_3, implies(((rho_23(pred_2) == pred_3) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_2_x(pred_2)) * (a_3_x(pred_3) - a_2_x(pred_2))) + ((a_3_y(pred_3) - a_2_y(pred_2)) * (a_3_y(pred_3) - a_2_y(pred_2))) + ((a_3_z(pred_3) - a_2_z(pred_2)) * (a_3_z(pred_3) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_23, implies(((pwl_23 >= (int)segLower + 1) && (pwl_23 <= (int)segUpper)), (rho_primed_23(pwl_23) == rho_23(c.int_val(pwl_23)) + ((pwl_23 - c.int_val(pwl_23)) * (rho_23(c.int_val(pwl_23) + 1) - rho_23(c.int_val(pwl_23))))))));
			s.add(forall(pwl_32, implies(((pwl_32 >= (int)segLower + 1) && (pwl_32 <= (int)segUpper)), (rho_primed_32(pwl_32) == rho_32(c.int_val(pwl_32)) + ((pwl_32 - c.int_val(pwl_32)) * (rho_32(c.int_val(pwl_32) + 1) - rho_32(c.int_val(pwl_32))))))));
			
			//inverse re-timing
			s.add(forall(t_23, implies(((t_23 >= (int)segLower) && (t_23 <= (int)segUpper)), (rho_32(rho_23(t_23)) == t_23))));

			// ================ AGENT 2 AND AGENT 3 END ================ //
			
			if(s.check() == sat)
		    {
		    	std::string verdict = std::to_string(i) + " : Sat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    else
		    {
		    	std::string verdict = std::to_string(i) + " : Unsat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    
		    //reset solver
		    //s.reset();
		    
		    //build and show model
		    //model m = s.get_model();
    		//std::cout << m << "\n";
	    }
	}
	//return verdicts;
}

void runSolver_5(double eps, int segCount, double sigDur, int msgLim)
{
	//enable parallel mode
	//set_param("parallel.enable", true);
	
	//get data
	std::vector<std::vector<std::string>> agentData_0 = getData("agent_0.txt");
	std::vector<std::vector<std::string>> agentData_1 = getData("agent_1.txt");
	std::vector<std::vector<std::string>> agentData_2 = getData("agent_2.txt");
	std::vector<std::vector<std::string>> agentData_3 = getData("agent_3.txt");
	std::vector<std::vector<std::string>> agentData_4 = getData("agent_4.txt");
	
	//safety checks
	if(!(std::stod(agentData_0[0][0]) == 0 && std::stod(agentData_1[0][0]) == 0))
	{
		return;
	}
	
	if(std::stod(agentData_0[1][0]) != std::stod(agentData_1[1][0]))
	{
		return;
	}
	
	//second time-stamp on agent that is to be re-timed
	double t1 = std::stod(agentData_0[1][0]);
	
	//delta
	int delta = 0;
	
	//segment duration
	double segDur = sigDur / segCount;
	
	//check if the segment duration is smaller than the sampling period
	if(segDur < t1)
	{
		segCount = sigDur / t1;
	}
	
	//multiplier for normalization
	double mult = 1 / t1;
	
	//normalization of paramters
	eps *= mult;
	sigDur *= mult;
	segDur *= mult;
	
	//verdict vector
	std::vector<std::string> verdicts;
	
	#pragma omp parallel
	{
		#pragma omp for
		for(int i = 0; i < segCount; i++) 
	    {			
			//segment bounds
			double segLower = (i * segDur) - eps;
			double segUpper = (i + 1) * segDur;
			
		    context c;

		    //solver
		    solver s(c);
		    
		    //co-ord functions
		    func_decl a_0_x = function("a_0_x", c.int_sort(), c.real_sort());
		    func_decl a_0_y = function("a_0_y", c.int_sort(), c.real_sort());
		    func_decl a_0_z = function("a_0_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_1_x = function("a_1_x", c.int_sort(), c.real_sort());
		    func_decl a_1_y = function("a_1_y", c.int_sort(), c.real_sort());
		    func_decl a_1_z = function("a_1_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_2_x = function("a_2_x", c.int_sort(), c.real_sort());
		    func_decl a_2_y = function("a_2_y", c.int_sort(), c.real_sort());
		    func_decl a_2_z = function("a_2_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_3_x = function("a_3_x", c.int_sort(), c.real_sort());
		    func_decl a_3_y = function("a_3_y", c.int_sort(), c.real_sort());
		    func_decl a_3_z = function("a_3_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_4_x = function("a_4_x", c.int_sort(), c.real_sort());
		    func_decl a_4_y = function("a_4_y", c.int_sort(), c.real_sort());
		    func_decl a_4_z = function("a_4_z", c.int_sort(), c.real_sort());
		    
		    //populate co-ord functions
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_0.size())
		        {
		        	s.add(a_0_x(j) == c.real_val(agentData_0[j][1].c_str()));
		        	s.add(a_0_y(j) == c.real_val(agentData_0[j][2].c_str()));
		        	s.add(a_0_z(j) == c.real_val(agentData_0[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_1.size())
		        {
		        	s.add(a_1_x(j) == c.real_val(agentData_1[j][1].c_str()));
		        	s.add(a_1_y(j) == c.real_val(agentData_1[j][2].c_str()));
		        	s.add(a_1_z(j) == c.real_val(agentData_1[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_2.size())
		        {
		        	s.add(a_2_x(j) == c.real_val(agentData_2[j][1].c_str()));
		        	s.add(a_2_y(j) == c.real_val(agentData_2[j][2].c_str()));
		        	s.add(a_2_z(j) == c.real_val(agentData_2[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_3.size())
		        {
		        	s.add(a_3_x(j) == c.real_val(agentData_3[j][1].c_str()));
		        	s.add(a_3_y(j) == c.real_val(agentData_3[j][2].c_str()));
		        	s.add(a_3_z(j) == c.real_val(agentData_3[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_4.size())
		        {
		        	s.add(a_4_x(j) == c.real_val(agentData_4[j][1].c_str()));
		        	s.add(a_4_y(j) == c.real_val(agentData_4[j][2].c_str()));
		        	s.add(a_4_z(j) == c.real_val(agentData_4[j][3].c_str()));
				}
		    }
		    
		    //general smt variables		  
			expr pred_0 = c.int_const("pred_0");
			s.add(pred_0 >= (int)segLower + 1 && pred_0 <= (int)segUpper);
			
		    expr pred_1 = c.int_const("pred_1");
		    s.add(pred_1 >= (int)segLower + 1 && pred_1 <= (int)segUpper);
		    
		    expr pred_2 = c.int_const("pred_2");
		    s.add(pred_2 >= (int)segLower + 1 && pred_2 <= (int)segUpper);
		    
		    expr pred_3 = c.int_const("pred_3");
		    s.add(pred_3 >= (int)segLower + 1 && pred_3 <= (int)segUpper);
		    
		    expr pred_4 = c.int_const("pred_4");
		    s.add(pred_4 >= (int)segLower + 1 && pred_4 <= (int)segUpper);
		    
		    // =============== AGENT 0 AND AGENT 1 START =============== //
			
			//agent pair smt variables
			expr t_01 = c.int_const("t_01");
		    s.add(t_01 >= (int)segLower + 1 && t_01 <= (int)segUpper);
		    
		    expr t_before_01 = c.int_const("t_before_01");
		    expr t_after_01 = c.int_const("t_after_01");
		    s.add(t_before_01 >= (int)segLower + 1 && t_before_01 <= (int)segUpper && t_after_01 >= (int)segLower && t_after_01 <= (int)segUpper);
		    
		    func_decl rho_01 = function("rho_01", c.int_sort(), c.int_sort());
		    func_decl rho_primed_01 = function("rho_primed_01", c.real_sort(), c.real_sort());
		    
		    func_decl rho_10 = function("rho_10", c.int_sort(), c.int_sort());
		    func_decl rho_primed_10 = function("rho_primed_10", c.real_sort(), c.real_sort());
		    
		    expr pwl_01 = c.int_const("pwl_01");
		    s.add(pwl_01 >= (int)segLower + 1 && pwl_01 <= (int)segUpper);
		    
		    expr pwl_10 = c.int_const("pwl_10");
		    s.add(pwl_10 >= (int)segLower + 1 && pwl_10 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_01, t_after_01, implies(((t_before_01 < t_after_01) && (t_before_01 >= (int)segLower + 1) && (t_before_01 <= (int)segUpper) && (t_after_01 >= (int)segLower) && (t_after_01 <= (int)segUpper)), ((rho_01(t_before_01) < rho_01(t_after_01)) && (rho_10(t_before_01) < rho_10(t_after_01))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_1, implies(((rho_01(pred_0) == pred_1) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_1 >= (int)segLower) && (pred_1 <= (int)segUpper)), (c.real_val(delta) <= (((a_1_x(pred_1) - a_0_x(pred_0)) * (a_1_x(pred_1) - a_0_x(pred_0))) + ((a_1_y(pred_1) - a_0_y(pred_0)) * (a_1_y(pred_1) - a_0_y(pred_0))) + ((a_1_z(pred_1) - a_0_z(pred_0)) * (a_1_z(pred_1) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_01, implies(((pwl_01 >= (int)segLower + 1) && (pwl_01 <= (int)segUpper)), (rho_primed_01(pwl_01) == rho_01(c.int_val(pwl_01)) + ((pwl_01 - c.int_val(pwl_01)) * (rho_01(c.int_val(pwl_01) + 1) - rho_01(c.int_val(pwl_01))))))));
			s.add(forall(pwl_10, implies(((pwl_10 >= (int)segLower + 1) && (pwl_10 <= (int)segUpper)), (rho_primed_10(pwl_10) == rho_10(c.int_val(pwl_10)) + ((pwl_10 - c.int_val(pwl_10)) * (rho_10(c.int_val(pwl_10) + 1) - rho_10(c.int_val(pwl_10))))))));
			
			//inverse re-timing
			s.add(forall(t_01, implies(((t_01 >= (int)segLower) && (t_01 <= (int)segUpper)), (rho_10(rho_01(t_01)) == t_01))));

			// ================ AGENT 0 AND AGENT 1 END ================ //
			
			// =============== AGENT 0 AND AGENT 2 START =============== //
			
			//agent pair smt variables
			expr t_02 = c.int_const("t_02");
		    s.add(t_02 >= (int)segLower + 1 && t_02 <= (int)segUpper);
		    
		    expr t_before_02 = c.int_const("t_before_02");
		    expr t_after_02 = c.int_const("t_after_02");
		    s.add(t_before_02 >= (int)segLower + 1 && t_before_02 <= (int)segUpper && t_after_02 >= (int)segLower && t_after_02 <= (int)segUpper);
		    
		    func_decl rho_02 = function("rho_02", c.int_sort(), c.int_sort());
		    func_decl rho_primed_02 = function("rho_primed_02", c.real_sort(), c.real_sort());
		    
		    func_decl rho_20 = function("rho_20", c.int_sort(), c.int_sort());
		    func_decl rho_primed_20 = function("rho_primed_20", c.real_sort(), c.real_sort());
		    
		    expr pwl_02 = c.int_const("pwl_02");
		    s.add(pwl_02 >= (int)segLower + 1 && pwl_02 <= (int)segUpper);
		    
		    expr pwl_20 = c.int_const("pwl_20");
		    s.add(pwl_20 >= (int)segLower + 1 && pwl_20 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_02(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_02(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_20(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_20(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_02, t_after_02, implies(((t_before_02 < t_after_02) && (t_before_02 >= (int)segLower + 1) && (t_before_02 <= (int)segUpper) && (t_after_02 >= (int)segLower) && (t_after_02 <= (int)segUpper)), ((rho_02(t_before_02) < rho_02(t_after_02)) && (rho_20(t_before_02) < rho_20(t_after_02))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_2, implies(((rho_02(pred_0) == pred_2) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_2 >= (int)segLower) && (pred_2 <= (int)segUpper)), (c.real_val(delta) <= (((a_2_x(pred_2) - a_0_x(pred_0)) * (a_2_x(pred_2) - a_0_x(pred_0))) + ((a_2_y(pred_2) - a_0_y(pred_0)) * (a_2_y(pred_2) - a_0_y(pred_0))) + ((a_2_z(pred_2) - a_0_z(pred_0)) * (a_2_z(pred_2) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_02, implies(((pwl_02 >= (int)segLower + 1) && (pwl_02 <= (int)segUpper)), (rho_primed_02(pwl_02) == rho_02(c.int_val(pwl_02)) + ((pwl_02 - c.int_val(pwl_02)) * (rho_02(c.int_val(pwl_02) + 1) - rho_02(c.int_val(pwl_02))))))));
			s.add(forall(pwl_20, implies(((pwl_20 >= (int)segLower + 1) && (pwl_20 <= (int)segUpper)), (rho_primed_20(pwl_20) == rho_20(c.int_val(pwl_20)) + ((pwl_20 - c.int_val(pwl_20)) * (rho_20(c.int_val(pwl_20) + 1) - rho_20(c.int_val(pwl_20))))))));
			
			//inverse re-timing
			s.add(forall(t_02, implies(((t_02 >= (int)segLower) && (t_02 <= (int)segUpper)), (rho_20(rho_02(t_02)) == t_02))));

			// ================ AGENT 0 AND AGENT 2 END ================ //
			
			// =============== AGENT 0 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_03 = c.int_const("t_03");
		    s.add(t_03 >= (int)segLower + 1 && t_03 <= (int)segUpper);
		    
		    expr t_before_03 = c.int_const("t_before_03");
		    expr t_after_03 = c.int_const("t_after_03");
		    s.add(t_before_03 >= (int)segLower + 1 && t_before_03 <= (int)segUpper && t_after_03 >= (int)segLower && t_after_03 <= (int)segUpper);
		    
		    func_decl rho_03 = function("rho_03", c.int_sort(), c.int_sort());
		    func_decl rho_primed_03 = function("rho_primed_03", c.real_sort(), c.real_sort());
		    
		    func_decl rho_30 = function("rho_30", c.int_sort(), c.int_sort());
		    func_decl rho_primed_30 = function("rho_primed_30", c.real_sort(), c.real_sort());
		    
		    expr pwl_03 = c.int_const("pwl_03");
		    s.add(pwl_03 >= (int)segLower + 1 && pwl_03 <= (int)segUpper);
		    
		    expr pwl_30 = c.int_const("pwl_30");
		    s.add(pwl_30 >= (int)segLower + 1 && pwl_30 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_03(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_03(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_30(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_30(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_03, t_after_03, implies(((t_before_03 < t_after_03) && (t_before_03 >= (int)segLower + 1) && (t_before_03 <= (int)segUpper) && (t_after_03 >= (int)segLower) && (t_after_03 <= (int)segUpper)), ((rho_03(t_before_03) < rho_03(t_after_03)) && (rho_30(t_before_03) < rho_30(t_after_03))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_3, implies(((rho_03(pred_0) == pred_3) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_0_x(pred_0)) * (a_3_x(pred_3) - a_0_x(pred_0))) + ((a_3_y(pred_3) - a_0_y(pred_0)) * (a_3_y(pred_3) - a_0_y(pred_0))) + ((a_3_z(pred_3) - a_0_z(pred_0)) * (a_3_z(pred_3) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_03, implies(((pwl_03 >= (int)segLower + 1) && (pwl_03 <= (int)segUpper)), (rho_primed_03(pwl_03) == rho_03(c.int_val(pwl_03)) + ((pwl_03 - c.int_val(pwl_03)) * (rho_03(c.int_val(pwl_03) + 1) - rho_03(c.int_val(pwl_03))))))));
			s.add(forall(pwl_30, implies(((pwl_30 >= (int)segLower + 1) && (pwl_30 <= (int)segUpper)), (rho_primed_30(pwl_30) == rho_30(c.int_val(pwl_30)) + ((pwl_30 - c.int_val(pwl_30)) * (rho_30(c.int_val(pwl_30) + 1) - rho_30(c.int_val(pwl_30))))))));
			
			//inverse re-timing
			s.add(forall(t_03, implies(((t_03 >= (int)segLower) && (t_03 <= (int)segUpper)), (rho_30(rho_03(t_03)) == t_03))));

			// ================ AGENT 0 AND AGENT 3 END ================ //
			
			// =============== AGENT 0 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_04 = c.int_const("t_04");
		    s.add(t_04 >= (int)segLower + 1 && t_04 <= (int)segUpper);
		    
		    expr t_before_04 = c.int_const("t_before_04");
		    expr t_after_04 = c.int_const("t_after_04");
		    s.add(t_before_04 >= (int)segLower + 1 && t_before_04 <= (int)segUpper && t_after_04 >= (int)segLower && t_after_04 <= (int)segUpper);
		    
		    func_decl rho_04 = function("rho_04", c.int_sort(), c.int_sort());
		    func_decl rho_primed_04 = function("rho_primed_04", c.real_sort(), c.real_sort());
		    
		    func_decl rho_40 = function("rho_40", c.int_sort(), c.int_sort());
		    func_decl rho_primed_40 = function("rho_primed_40", c.real_sort(), c.real_sort());
		    
		    expr pwl_04 = c.int_const("pwl_04");
		    s.add(pwl_04 >= (int)segLower + 1 && pwl_04 <= (int)segUpper);
		    
		    expr pwl_40 = c.int_const("pwl_40");
		    s.add(pwl_40 >= (int)segLower + 1 && pwl_40 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_04(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_04(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_40(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_40(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_04, t_after_04, implies(((t_before_04 < t_after_04) && (t_before_04 >= (int)segLower + 1) && (t_before_04 <= (int)segUpper) && (t_after_04 >= (int)segLower) && (t_after_04 <= (int)segUpper)), ((rho_04(t_before_04) < rho_04(t_after_04)) && (rho_40(t_before_04) < rho_40(t_after_04))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_4, implies(((rho_04(pred_0) == pred_4) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_0_x(pred_0)) * (a_4_x(pred_4) - a_0_x(pred_0))) + ((a_4_y(pred_4) - a_0_y(pred_0)) * (a_4_y(pred_4) - a_0_y(pred_0))) + ((a_4_z(pred_4) - a_0_z(pred_0)) * (a_4_z(pred_4) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_04, implies(((pwl_04 >= (int)segLower + 1) && (pwl_04 <= (int)segUpper)), (rho_primed_04(pwl_04) == rho_04(c.int_val(pwl_04)) + ((pwl_04 - c.int_val(pwl_04)) * (rho_04(c.int_val(pwl_04) + 1) - rho_04(c.int_val(pwl_04))))))));
			s.add(forall(pwl_40, implies(((pwl_40 >= (int)segLower + 1) && (pwl_40 <= (int)segUpper)), (rho_primed_40(pwl_40) == rho_40(c.int_val(pwl_40)) + ((pwl_40 - c.int_val(pwl_40)) * (rho_40(c.int_val(pwl_40) + 1) - rho_40(c.int_val(pwl_40))))))));
			
			//inverse re-timing
			s.add(forall(t_04, implies(((t_04 >= (int)segLower) && (t_04 <= (int)segUpper)), (rho_40(rho_04(t_04)) == t_04))));

			// ================ AGENT 0 AND AGENT 4 END ================ //
			
			// =============== AGENT 1 AND AGENT 2 START =============== //
			
			//agent pair smt variables
			expr t_12 = c.int_const("t_12");
		    s.add(t_12 >= (int)segLower + 1 && t_12 <= (int)segUpper);
		    
		    expr t_before_12 = c.int_const("t_before_12");
		    expr t_after_12 = c.int_const("t_after_12");
		    s.add(t_before_12 >= (int)segLower + 1 && t_before_12 <= (int)segUpper && t_after_12 >= (int)segLower && t_after_12 <= (int)segUpper);
		    
		    func_decl rho_12 = function("rho_12", c.int_sort(), c.int_sort());
		    func_decl rho_primed_12 = function("rho_primed_12", c.real_sort(), c.real_sort());
		    
		    func_decl rho_21 = function("rho_21", c.int_sort(), c.int_sort());
		    func_decl rho_primed_21 = function("rho_primed_21", c.real_sort(), c.real_sort());
		    
		    expr pwl_12 = c.int_const("pwl_12");
		    s.add(pwl_12 >= (int)segLower + 1 && pwl_12 <= (int)segUpper);
		    
		    expr pwl_21 = c.int_const("pwl_21");
		    s.add(pwl_21 >= (int)segLower + 1 && pwl_21 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_12(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_12(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_21(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_21(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_12, t_after_12, implies(((t_before_12 < t_after_12) && (t_before_12 >= (int)segLower + 1) && (t_before_12 <= (int)segUpper) && (t_after_12 >= (int)segLower) && (t_after_12 <= (int)segUpper)), ((rho_12(t_before_12) < rho_12(t_after_12)) && (rho_21(t_before_12) < rho_21(t_after_12))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_2, implies(((rho_12(pred_1) == pred_2) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_2 >= (int)segLower) && (pred_2 <= (int)segUpper)), (c.real_val(delta) <= (((a_2_x(pred_2) - a_1_x(pred_1)) * (a_2_x(pred_2) - a_1_x(pred_1))) + ((a_2_y(pred_2) - a_1_y(pred_1)) * (a_2_y(pred_2) - a_1_y(pred_1))) + ((a_2_z(pred_2) - a_1_z(pred_1)) * (a_2_z(pred_2) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_12, implies(((pwl_12 >= (int)segLower + 1) && (pwl_12 <= (int)segUpper)), (rho_primed_12(pwl_12) == rho_12(c.int_val(pwl_12)) + ((pwl_12 - c.int_val(pwl_12)) * (rho_12(c.int_val(pwl_12) + 1) - rho_12(c.int_val(pwl_12))))))));
			s.add(forall(pwl_21, implies(((pwl_21 >= (int)segLower + 1) && (pwl_21 <= (int)segUpper)), (rho_primed_21(pwl_21) == rho_21(c.int_val(pwl_21)) + ((pwl_21 - c.int_val(pwl_21)) * (rho_21(c.int_val(pwl_21) + 1) - rho_21(c.int_val(pwl_21))))))));
			
			//inverse re-timing
			s.add(forall(t_12, implies(((t_12 >= (int)segLower) && (t_12 <= (int)segUpper)), (rho_21(rho_12(t_12)) == t_12))));

			// ================ AGENT 1 AND AGENT 2 END ================ //
			
			// =============== AGENT 1 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_13 = c.int_const("t_13");
		    s.add(t_13 >= (int)segLower + 1 && t_13 <= (int)segUpper);
		    
		    expr t_before_13 = c.int_const("t_before_13");
		    expr t_after_13 = c.int_const("t_after_13");
		    s.add(t_before_13 >= (int)segLower + 1 && t_before_13 <= (int)segUpper && t_after_13 >= (int)segLower && t_after_13 <= (int)segUpper);
		    
		    func_decl rho_13 = function("rho_13", c.int_sort(), c.int_sort());
		    func_decl rho_primed_13 = function("rho_primed_13", c.real_sort(), c.real_sort());
		    
		    func_decl rho_31 = function("rho_31", c.int_sort(), c.int_sort());
		    func_decl rho_primed_31 = function("rho_primed_31", c.real_sort(), c.real_sort());
		    
		    expr pwl_13 = c.int_const("pwl_13");
		    s.add(pwl_13 >= (int)segLower + 1 && pwl_13 <= (int)segUpper);
		    
		    expr pwl_31 = c.int_const("pwl_31");
		    s.add(pwl_31 >= (int)segLower + 1 && pwl_31 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_13(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_13(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_31(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_31(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_13, t_after_13, implies(((t_before_13 < t_after_13) && (t_before_13 >= (int)segLower + 1) && (t_before_13 <= (int)segUpper) && (t_after_13 >= (int)segLower) && (t_after_13 <= (int)segUpper)), ((rho_13(t_before_13) < rho_13(t_after_13)) && (rho_31(t_before_13) < rho_31(t_after_13))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_3, implies(((rho_13(pred_1) == pred_3) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_1_x(pred_1)) * (a_3_x(pred_3) - a_1_x(pred_1))) + ((a_3_y(pred_3) - a_1_y(pred_1)) * (a_3_y(pred_3) - a_1_y(pred_1))) + ((a_3_z(pred_3) - a_1_z(pred_1)) * (a_3_z(pred_3) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_13, implies(((pwl_13 >= (int)segLower + 1) && (pwl_13 <= (int)segUpper)), (rho_primed_13(pwl_13) == rho_13(c.int_val(pwl_13)) + ((pwl_13 - c.int_val(pwl_13)) * (rho_13(c.int_val(pwl_13) + 1) - rho_13(c.int_val(pwl_13))))))));
			s.add(forall(pwl_31, implies(((pwl_31 >= (int)segLower + 1) && (pwl_31 <= (int)segUpper)), (rho_primed_31(pwl_31) == rho_31(c.int_val(pwl_31)) + ((pwl_31 - c.int_val(pwl_31)) * (rho_31(c.int_val(pwl_31) + 1) - rho_31(c.int_val(pwl_31))))))));
			
			//inverse re-timing
			s.add(forall(t_13, implies(((t_13 >= (int)segLower) && (t_13 <= (int)segUpper)), (rho_31(rho_13(t_13)) == t_13))));

			// ================ AGENT 1 AND AGENT 3 END ================ //
			
			// =============== AGENT 1 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_14 = c.int_const("t_14");
		    s.add(t_14 >= (int)segLower + 1 && t_14 <= (int)segUpper);
		    
		    expr t_before_14 = c.int_const("t_before_14");
		    expr t_after_14 = c.int_const("t_after_14");
		    s.add(t_before_14 >= (int)segLower + 1 && t_before_14 <= (int)segUpper && t_after_14 >= (int)segLower && t_after_14 <= (int)segUpper);
		    
		    func_decl rho_14 = function("rho_14", c.int_sort(), c.int_sort());
		    func_decl rho_primed_14 = function("rho_primed_14", c.real_sort(), c.real_sort());
		    
		    func_decl rho_41 = function("rho_41", c.int_sort(), c.int_sort());
		    func_decl rho_primed_41 = function("rho_primed_41", c.real_sort(), c.real_sort());
		    
		    expr pwl_14 = c.int_const("pwl_14");
		    s.add(pwl_14 >= (int)segLower + 1 && pwl_14 <= (int)segUpper);
		    
		    expr pwl_41 = c.int_const("pwl_41");
		    s.add(pwl_41 >= (int)segLower + 1 && pwl_41 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_14(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_14(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_41(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_41(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_14, t_after_14, implies(((t_before_14 < t_after_14) && (t_before_14 >= (int)segLower + 1) && (t_before_14 <= (int)segUpper) && (t_after_14 >= (int)segLower) && (t_after_14 <= (int)segUpper)), ((rho_14(t_before_14) < rho_14(t_after_14)) && (rho_41(t_before_14) < rho_41(t_after_14))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_4, implies(((rho_14(pred_1) == pred_4) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_1_x(pred_1)) * (a_4_x(pred_4) - a_1_x(pred_1))) + ((a_4_y(pred_4) - a_1_y(pred_1)) * (a_4_y(pred_4) - a_1_y(pred_1))) + ((a_4_z(pred_4) - a_1_z(pred_1)) * (a_4_z(pred_4) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_14, implies(((pwl_14 >= (int)segLower + 1) && (pwl_14 <= (int)segUpper)), (rho_primed_14(pwl_14) == rho_14(c.int_val(pwl_14)) + ((pwl_14 - c.int_val(pwl_14)) * (rho_14(c.int_val(pwl_14) + 1) - rho_14(c.int_val(pwl_14))))))));
			s.add(forall(pwl_41, implies(((pwl_41 >= (int)segLower + 1) && (pwl_41 <= (int)segUpper)), (rho_primed_41(pwl_41) == rho_41(c.int_val(pwl_41)) + ((pwl_41 - c.int_val(pwl_41)) * (rho_41(c.int_val(pwl_41) + 1) - rho_41(c.int_val(pwl_41))))))));
			
			//inverse re-timing
			s.add(forall(t_14, implies(((t_14 >= (int)segLower) && (t_14 <= (int)segUpper)), (rho_41(rho_14(t_14)) == t_14))));

			// ================ AGENT 1 AND AGENT 4 END ================ //
			
			// =============== AGENT 2 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_23 = c.int_const("t_23");
		    s.add(t_23 >= (int)segLower + 1 && t_23 <= (int)segUpper);
		    
		    expr t_before_23 = c.int_const("t_before_23");
		    expr t_after_23 = c.int_const("t_after_23");
		    s.add(t_before_23 >= (int)segLower + 1 && t_before_23 <= (int)segUpper && t_after_23 >= (int)segLower && t_after_23 <= (int)segUpper);
		    
		    func_decl rho_23 = function("rho_23", c.int_sort(), c.int_sort());
		    func_decl rho_primed_23 = function("rho_primed_23", c.real_sort(), c.real_sort());
		    
		    func_decl rho_32 = function("rho_32", c.int_sort(), c.int_sort());
		    func_decl rho_primed_32 = function("rho_primed_32", c.real_sort(), c.real_sort());
		    
		    expr pwl_23 = c.int_const("pwl_23");
		    s.add(pwl_23 >= (int)segLower + 1 && pwl_23 <= (int)segUpper);
		    
		    expr pwl_32 = c.int_const("pwl_32");
		    s.add(pwl_32 >= (int)segLower + 1 && pwl_32 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_23(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_23(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_32(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_32(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_23, t_after_23, implies(((t_before_23 < t_after_23) && (t_before_23 >= (int)segLower + 1) && (t_before_23 <= (int)segUpper) && (t_after_23 >= (int)segLower) && (t_after_23 <= (int)segUpper)), ((rho_23(t_before_23) < rho_23(t_after_23)) && (rho_32(t_before_23) < rho_32(t_after_23))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_3, implies(((rho_23(pred_2) == pred_3) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_2_x(pred_2)) * (a_3_x(pred_3) - a_2_x(pred_2))) + ((a_3_y(pred_3) - a_2_y(pred_2)) * (a_3_y(pred_3) - a_2_y(pred_2))) + ((a_3_z(pred_3) - a_2_z(pred_2)) * (a_3_z(pred_3) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_23, implies(((pwl_23 >= (int)segLower + 1) && (pwl_23 <= (int)segUpper)), (rho_primed_23(pwl_23) == rho_23(c.int_val(pwl_23)) + ((pwl_23 - c.int_val(pwl_23)) * (rho_23(c.int_val(pwl_23) + 1) - rho_23(c.int_val(pwl_23))))))));
			s.add(forall(pwl_32, implies(((pwl_32 >= (int)segLower + 1) && (pwl_32 <= (int)segUpper)), (rho_primed_32(pwl_32) == rho_32(c.int_val(pwl_32)) + ((pwl_32 - c.int_val(pwl_32)) * (rho_32(c.int_val(pwl_32) + 1) - rho_32(c.int_val(pwl_32))))))));
			
			//inverse re-timing
			s.add(forall(t_23, implies(((t_23 >= (int)segLower) && (t_23 <= (int)segUpper)), (rho_32(rho_23(t_23)) == t_23))));

			// ================ AGENT 2 AND AGENT 3 END ================ //
			
			// =============== AGENT 2 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_24 = c.int_const("t_24");
		    s.add(t_24 >= (int)segLower + 1 && t_24 <= (int)segUpper);
		    
		    expr t_before_24 = c.int_const("t_before_24");
		    expr t_after_24 = c.int_const("t_after_24");
		    s.add(t_before_24 >= (int)segLower + 1 && t_before_24 <= (int)segUpper && t_after_24 >= (int)segLower && t_after_24 <= (int)segUpper);
		    
		    func_decl rho_24 = function("rho_24", c.int_sort(), c.int_sort());
		    func_decl rho_primed_24 = function("rho_primed_24", c.real_sort(), c.real_sort());
		    
		    func_decl rho_42 = function("rho_42", c.int_sort(), c.int_sort());
		    func_decl rho_primed_42 = function("rho_primed_42", c.real_sort(), c.real_sort());
		    
		    expr pwl_24 = c.int_const("pwl_24");
		    s.add(pwl_24 >= (int)segLower + 1 && pwl_24 <= (int)segUpper);
		    
		    expr pwl_42 = c.int_const("pwl_42");
		    s.add(pwl_42 >= (int)segLower + 1 && pwl_42 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_24(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_24(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_42(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_42(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_24, t_after_24, implies(((t_before_24 < t_after_24) && (t_before_24 >= (int)segLower + 1) && (t_before_24 <= (int)segUpper) && (t_after_24 >= (int)segLower) && (t_after_24 <= (int)segUpper)), ((rho_24(t_before_24) < rho_24(t_after_24)) && (rho_42(t_before_24) < rho_42(t_after_24))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_4, implies(((rho_24(pred_2) == pred_4) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_2_x(pred_2)) * (a_4_x(pred_4) - a_2_x(pred_2))) + ((a_4_y(pred_4) - a_2_y(pred_2)) * (a_4_y(pred_4) - a_2_y(pred_2))) + ((a_4_z(pred_4) - a_2_z(pred_2)) * (a_4_z(pred_4) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_24, implies(((pwl_24 >= (int)segLower + 1) && (pwl_24 <= (int)segUpper)), (rho_primed_24(pwl_24) == rho_24(c.int_val(pwl_24)) + ((pwl_24 - c.int_val(pwl_24)) * (rho_24(c.int_val(pwl_24) + 1) - rho_24(c.int_val(pwl_24))))))));
			s.add(forall(pwl_42, implies(((pwl_42 >= (int)segLower + 1) && (pwl_42 <= (int)segUpper)), (rho_primed_42(pwl_42) == rho_42(c.int_val(pwl_42)) + ((pwl_42 - c.int_val(pwl_42)) * (rho_42(c.int_val(pwl_42) + 1) - rho_42(c.int_val(pwl_42))))))));
			
			//inverse re-timing
			s.add(forall(t_24, implies(((t_24 >= (int)segLower) && (t_24 <= (int)segUpper)), (rho_42(rho_24(t_24)) == t_24))));

			// ================ AGENT 2 AND AGENT 4 END ================ //
			
			// =============== AGENT 3 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_34 = c.int_const("t_34");
		    s.add(t_34 >= (int)segLower + 1 && t_34 <= (int)segUpper);
		    
		    expr t_before_34 = c.int_const("t_before_34");
		    expr t_after_34 = c.int_const("t_after_34");
		    s.add(t_before_34 >= (int)segLower + 1 && t_before_34 <= (int)segUpper && t_after_34 >= (int)segLower && t_after_34 <= (int)segUpper);
		    
		    func_decl rho_34 = function("rho_34", c.int_sort(), c.int_sort());
		    func_decl rho_primed_34 = function("rho_primed_34", c.real_sort(), c.real_sort());
		    
		    func_decl rho_43 = function("rho_43", c.int_sort(), c.int_sort());
		    func_decl rho_primed_43 = function("rho_primed_43", c.real_sort(), c.real_sort());
		    
		    expr pwl_34 = c.int_const("pwl_34");
		    s.add(pwl_34 >= (int)segLower + 1 && pwl_34 <= (int)segUpper);
		    
		    expr pwl_43 = c.int_const("pwl_43");
		    s.add(pwl_43 >= (int)segLower + 1 && pwl_43 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_34(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_34(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_43(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_43(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_34, t_after_34, implies(((t_before_34 < t_after_34) && (t_before_34 >= (int)segLower + 1) && (t_before_34 <= (int)segUpper) && (t_after_34 >= (int)segLower) && (t_after_34 <= (int)segUpper)), ((rho_34(t_before_34) < rho_34(t_after_34)) && (rho_43(t_before_34) < rho_43(t_after_34))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_4, implies(((rho_34(pred_3) == pred_4) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_3_x(pred_3)) * (a_4_x(pred_4) - a_3_x(pred_3))) + ((a_4_y(pred_4) - a_3_y(pred_3)) * (a_4_y(pred_4) - a_3_y(pred_3))) + ((a_4_z(pred_4) - a_3_z(pred_3)) * (a_4_z(pred_4) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_34, implies(((pwl_34 >= (int)segLower + 1) && (pwl_34 <= (int)segUpper)), (rho_primed_34(pwl_34) == rho_34(c.int_val(pwl_34)) + ((pwl_34 - c.int_val(pwl_34)) * (rho_34(c.int_val(pwl_34) + 1) - rho_34(c.int_val(pwl_34))))))));
			s.add(forall(pwl_43, implies(((pwl_43 >= (int)segLower + 1) && (pwl_43 <= (int)segUpper)), (rho_primed_43(pwl_43) == rho_43(c.int_val(pwl_43)) + ((pwl_43 - c.int_val(pwl_43)) * (rho_43(c.int_val(pwl_43) + 1) - rho_43(c.int_val(pwl_43))))))));
			
			//inverse re-timing
			s.add(forall(t_34, implies(((t_34 >= (int)segLower) && (t_34 <= (int)segUpper)), (rho_43(rho_34(t_34)) == t_34))));

			// ================ AGENT 3 AND AGENT 4 END ================ //
			
			if(s.check() == sat)
		    {
		    	std::string verdict = std::to_string(i) + " : Sat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    else
		    {
		    	std::string verdict = std::to_string(i) + " : Unsat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    
		    //reset solver
		    //s.reset();
		    
		    //build and show model
		    //model m = s.get_model();
    		//std::cout << m << "\n";
	    }
	}
	//return verdicts;
}

void runSolver_6(double eps, int segCount, double sigDur, int msgLim)
{
	//enable parallel mode
	//set_param("parallel.enable", true);
	
	//get data
	std::vector<std::vector<std::string>> agentData_0 = getData("agent_0.txt");
	std::vector<std::vector<std::string>> agentData_1 = getData("agent_1.txt");
	std::vector<std::vector<std::string>> agentData_2 = getData("agent_2.txt");
	std::vector<std::vector<std::string>> agentData_3 = getData("agent_3.txt");
	std::vector<std::vector<std::string>> agentData_4 = getData("agent_4.txt");
	std::vector<std::vector<std::string>> agentData_5 = getData("agent_5.txt");
	
	//safety checks
	if(!(std::stod(agentData_0[0][0]) == 0 && std::stod(agentData_1[0][0]) == 0))
	{
		return;
	}
	
	if(std::stod(agentData_0[1][0]) != std::stod(agentData_1[1][0]))
	{
		return;
	}
	
	//second time-stamp on agent that is to be re-timed
	double t1 = std::stod(agentData_0[1][0]);
	
	//delta
	int delta = 0;
	
	//segment duration
	double segDur = sigDur / segCount;
	
	//check if the segment duration is smaller than the sampling period
	if(segDur < t1)
	{
		segCount = sigDur / t1;
	}
	
	//multiplier for normalization
	double mult = 1 / t1;
	
	//normalization of paramters
	eps *= mult;
	sigDur *= mult;
	segDur *= mult;
	
	//verdict vector
	std::vector<std::string> verdicts;
	
	#pragma omp parallel
	{
		#pragma omp for
		for(int i = 0; i < segCount; i++) 
	    {			
			//segment bounds
			double segLower = (i * segDur) - eps;
			double segUpper = (i + 1) * segDur;
			
		    context c;

		    //solver
		    solver s(c);
		    
		    //co-ord functions
		    func_decl a_0_x = function("a_0_x", c.int_sort(), c.real_sort());
		    func_decl a_0_y = function("a_0_y", c.int_sort(), c.real_sort());
		    func_decl a_0_z = function("a_0_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_1_x = function("a_1_x", c.int_sort(), c.real_sort());
		    func_decl a_1_y = function("a_1_y", c.int_sort(), c.real_sort());
		    func_decl a_1_z = function("a_1_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_2_x = function("a_2_x", c.int_sort(), c.real_sort());
		    func_decl a_2_y = function("a_2_y", c.int_sort(), c.real_sort());
		    func_decl a_2_z = function("a_2_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_3_x = function("a_3_x", c.int_sort(), c.real_sort());
		    func_decl a_3_y = function("a_3_y", c.int_sort(), c.real_sort());
		    func_decl a_3_z = function("a_3_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_4_x = function("a_4_x", c.int_sort(), c.real_sort());
		    func_decl a_4_y = function("a_4_y", c.int_sort(), c.real_sort());
		    func_decl a_4_z = function("a_4_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_5_x = function("a_5_x", c.int_sort(), c.real_sort());
		    func_decl a_5_y = function("a_5_y", c.int_sort(), c.real_sort());
		    func_decl a_5_z = function("a_5_z", c.int_sort(), c.real_sort());
		    
		    //populate co-ord functions
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_0.size())
		        {
		        	s.add(a_0_x(j) == c.real_val(agentData_0[j][1].c_str()));
		        	s.add(a_0_y(j) == c.real_val(agentData_0[j][2].c_str()));
		        	s.add(a_0_z(j) == c.real_val(agentData_0[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_1.size())
		        {
		        	s.add(a_1_x(j) == c.real_val(agentData_1[j][1].c_str()));
		        	s.add(a_1_y(j) == c.real_val(agentData_1[j][2].c_str()));
		        	s.add(a_1_z(j) == c.real_val(agentData_1[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_2.size())
		        {
		        	s.add(a_2_x(j) == c.real_val(agentData_2[j][1].c_str()));
		        	s.add(a_2_y(j) == c.real_val(agentData_2[j][2].c_str()));
		        	s.add(a_2_z(j) == c.real_val(agentData_2[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_3.size())
		        {
		        	s.add(a_3_x(j) == c.real_val(agentData_3[j][1].c_str()));
		        	s.add(a_3_y(j) == c.real_val(agentData_3[j][2].c_str()));
		        	s.add(a_3_z(j) == c.real_val(agentData_3[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_4.size())
		        {
		        	s.add(a_4_x(j) == c.real_val(agentData_4[j][1].c_str()));
		        	s.add(a_4_y(j) == c.real_val(agentData_4[j][2].c_str()));
		        	s.add(a_4_z(j) == c.real_val(agentData_4[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_5.size())
		        {
		        	s.add(a_5_x(j) == c.real_val(agentData_5[j][1].c_str()));
		        	s.add(a_5_y(j) == c.real_val(agentData_5[j][2].c_str()));
		        	s.add(a_5_z(j) == c.real_val(agentData_5[j][3].c_str()));
				}
		    }
		    
		    //general smt variables		  
			expr pred_0 = c.int_const("pred_0");
			s.add(pred_0 >= (int)segLower + 1 && pred_0 <= (int)segUpper);
			
		    expr pred_1 = c.int_const("pred_1");
		    s.add(pred_1 >= (int)segLower + 1 && pred_1 <= (int)segUpper);
		    
		    expr pred_2 = c.int_const("pred_2");
		    s.add(pred_2 >= (int)segLower + 1 && pred_2 <= (int)segUpper);
		    
		    expr pred_3 = c.int_const("pred_3");
		    s.add(pred_3 >= (int)segLower + 1 && pred_3 <= (int)segUpper);
		    
		    expr pred_4 = c.int_const("pred_4");
		    s.add(pred_4 >= (int)segLower + 1 && pred_4 <= (int)segUpper);
		    
		    expr pred_5 = c.int_const("pred_5");
		    s.add(pred_5 >= (int)segLower + 1 && pred_5 <= (int)segUpper);
		    
		    // =============== AGENT 0 AND AGENT 1 START =============== //
			
			//agent pair smt variables
			expr t_01 = c.int_const("t_01");
		    s.add(t_01 >= (int)segLower + 1 && t_01 <= (int)segUpper);
		    
		    expr t_before_01 = c.int_const("t_before_01");
		    expr t_after_01 = c.int_const("t_after_01");
		    s.add(t_before_01 >= (int)segLower + 1 && t_before_01 <= (int)segUpper && t_after_01 >= (int)segLower && t_after_01 <= (int)segUpper);
		    
		    func_decl rho_01 = function("rho_01", c.int_sort(), c.int_sort());
		    func_decl rho_primed_01 = function("rho_primed_01", c.real_sort(), c.real_sort());
		    
		    func_decl rho_10 = function("rho_10", c.int_sort(), c.int_sort());
		    func_decl rho_primed_10 = function("rho_primed_10", c.real_sort(), c.real_sort());
		    
		    expr pwl_01 = c.int_const("pwl_01");
		    s.add(pwl_01 >= (int)segLower + 1 && pwl_01 <= (int)segUpper);
		    
		    expr pwl_10 = c.int_const("pwl_10");
		    s.add(pwl_10 >= (int)segLower + 1 && pwl_10 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_01, t_after_01, implies(((t_before_01 < t_after_01) && (t_before_01 >= (int)segLower + 1) && (t_before_01 <= (int)segUpper) && (t_after_01 >= (int)segLower) && (t_after_01 <= (int)segUpper)), ((rho_01(t_before_01) < rho_01(t_after_01)) && (rho_10(t_before_01) < rho_10(t_after_01))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_1, implies(((rho_01(pred_0) == pred_1) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_1 >= (int)segLower) && (pred_1 <= (int)segUpper)), (c.real_val(delta) <= (((a_1_x(pred_1) - a_0_x(pred_0)) * (a_1_x(pred_1) - a_0_x(pred_0))) + ((a_1_y(pred_1) - a_0_y(pred_0)) * (a_1_y(pred_1) - a_0_y(pred_0))) + ((a_1_z(pred_1) - a_0_z(pred_0)) * (a_1_z(pred_1) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_01, implies(((pwl_01 >= (int)segLower + 1) && (pwl_01 <= (int)segUpper)), (rho_primed_01(pwl_01) == rho_01(c.int_val(pwl_01)) + ((pwl_01 - c.int_val(pwl_01)) * (rho_01(c.int_val(pwl_01) + 1) - rho_01(c.int_val(pwl_01))))))));
			s.add(forall(pwl_10, implies(((pwl_10 >= (int)segLower + 1) && (pwl_10 <= (int)segUpper)), (rho_primed_10(pwl_10) == rho_10(c.int_val(pwl_10)) + ((pwl_10 - c.int_val(pwl_10)) * (rho_10(c.int_val(pwl_10) + 1) - rho_10(c.int_val(pwl_10))))))));
			
			//inverse re-timing
			s.add(forall(t_01, implies(((t_01 >= (int)segLower) && (t_01 <= (int)segUpper)), (rho_10(rho_01(t_01)) == t_01))));

			// ================ AGENT 0 AND AGENT 1 END ================ //
			
			// =============== AGENT 0 AND AGENT 2 START =============== //
			
			//agent pair smt variables
			expr t_02 = c.int_const("t_02");
		    s.add(t_02 >= (int)segLower + 1 && t_02 <= (int)segUpper);
		    
		    expr t_before_02 = c.int_const("t_before_02");
		    expr t_after_02 = c.int_const("t_after_02");
		    s.add(t_before_02 >= (int)segLower + 1 && t_before_02 <= (int)segUpper && t_after_02 >= (int)segLower && t_after_02 <= (int)segUpper);
		    
		    func_decl rho_02 = function("rho_02", c.int_sort(), c.int_sort());
		    func_decl rho_primed_02 = function("rho_primed_02", c.real_sort(), c.real_sort());
		    
		    func_decl rho_20 = function("rho_20", c.int_sort(), c.int_sort());
		    func_decl rho_primed_20 = function("rho_primed_20", c.real_sort(), c.real_sort());
		    
		    expr pwl_02 = c.int_const("pwl_02");
		    s.add(pwl_02 >= (int)segLower + 1 && pwl_02 <= (int)segUpper);
		    
		    expr pwl_20 = c.int_const("pwl_20");
		    s.add(pwl_20 >= (int)segLower + 1 && pwl_20 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_02(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_02(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_20(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_20(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_02, t_after_02, implies(((t_before_02 < t_after_02) && (t_before_02 >= (int)segLower + 1) && (t_before_02 <= (int)segUpper) && (t_after_02 >= (int)segLower) && (t_after_02 <= (int)segUpper)), ((rho_02(t_before_02) < rho_02(t_after_02)) && (rho_20(t_before_02) < rho_20(t_after_02))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_2, implies(((rho_02(pred_0) == pred_2) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_2 >= (int)segLower) && (pred_2 <= (int)segUpper)), (c.real_val(delta) <= (((a_2_x(pred_2) - a_0_x(pred_0)) * (a_2_x(pred_2) - a_0_x(pred_0))) + ((a_2_y(pred_2) - a_0_y(pred_0)) * (a_2_y(pred_2) - a_0_y(pred_0))) + ((a_2_z(pred_2) - a_0_z(pred_0)) * (a_2_z(pred_2) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_02, implies(((pwl_02 >= (int)segLower + 1) && (pwl_02 <= (int)segUpper)), (rho_primed_02(pwl_02) == rho_02(c.int_val(pwl_02)) + ((pwl_02 - c.int_val(pwl_02)) * (rho_02(c.int_val(pwl_02) + 1) - rho_02(c.int_val(pwl_02))))))));
			s.add(forall(pwl_20, implies(((pwl_20 >= (int)segLower + 1) && (pwl_20 <= (int)segUpper)), (rho_primed_20(pwl_20) == rho_20(c.int_val(pwl_20)) + ((pwl_20 - c.int_val(pwl_20)) * (rho_20(c.int_val(pwl_20) + 1) - rho_20(c.int_val(pwl_20))))))));
			
			//inverse re-timing
			s.add(forall(t_02, implies(((t_02 >= (int)segLower) && (t_02 <= (int)segUpper)), (rho_20(rho_02(t_02)) == t_02))));

			// ================ AGENT 0 AND AGENT 2 END ================ //
			
			// =============== AGENT 0 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_03 = c.int_const("t_03");
		    s.add(t_03 >= (int)segLower + 1 && t_03 <= (int)segUpper);
		    
		    expr t_before_03 = c.int_const("t_before_03");
		    expr t_after_03 = c.int_const("t_after_03");
		    s.add(t_before_03 >= (int)segLower + 1 && t_before_03 <= (int)segUpper && t_after_03 >= (int)segLower && t_after_03 <= (int)segUpper);
		    
		    func_decl rho_03 = function("rho_03", c.int_sort(), c.int_sort());
		    func_decl rho_primed_03 = function("rho_primed_03", c.real_sort(), c.real_sort());
		    
		    func_decl rho_30 = function("rho_30", c.int_sort(), c.int_sort());
		    func_decl rho_primed_30 = function("rho_primed_30", c.real_sort(), c.real_sort());
		    
		    expr pwl_03 = c.int_const("pwl_03");
		    s.add(pwl_03 >= (int)segLower + 1 && pwl_03 <= (int)segUpper);
		    
		    expr pwl_30 = c.int_const("pwl_30");
		    s.add(pwl_30 >= (int)segLower + 1 && pwl_30 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_03(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_03(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_30(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_30(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_03, t_after_03, implies(((t_before_03 < t_after_03) && (t_before_03 >= (int)segLower + 1) && (t_before_03 <= (int)segUpper) && (t_after_03 >= (int)segLower) && (t_after_03 <= (int)segUpper)), ((rho_03(t_before_03) < rho_03(t_after_03)) && (rho_30(t_before_03) < rho_30(t_after_03))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_3, implies(((rho_03(pred_0) == pred_3) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_0_x(pred_0)) * (a_3_x(pred_3) - a_0_x(pred_0))) + ((a_3_y(pred_3) - a_0_y(pred_0)) * (a_3_y(pred_3) - a_0_y(pred_0))) + ((a_3_z(pred_3) - a_0_z(pred_0)) * (a_3_z(pred_3) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_03, implies(((pwl_03 >= (int)segLower + 1) && (pwl_03 <= (int)segUpper)), (rho_primed_03(pwl_03) == rho_03(c.int_val(pwl_03)) + ((pwl_03 - c.int_val(pwl_03)) * (rho_03(c.int_val(pwl_03) + 1) - rho_03(c.int_val(pwl_03))))))));
			s.add(forall(pwl_30, implies(((pwl_30 >= (int)segLower + 1) && (pwl_30 <= (int)segUpper)), (rho_primed_30(pwl_30) == rho_30(c.int_val(pwl_30)) + ((pwl_30 - c.int_val(pwl_30)) * (rho_30(c.int_val(pwl_30) + 1) - rho_30(c.int_val(pwl_30))))))));
			
			//inverse re-timing
			s.add(forall(t_03, implies(((t_03 >= (int)segLower) && (t_03 <= (int)segUpper)), (rho_30(rho_03(t_03)) == t_03))));

			// ================ AGENT 0 AND AGENT 3 END ================ //
			
			// =============== AGENT 0 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_04 = c.int_const("t_04");
		    s.add(t_04 >= (int)segLower + 1 && t_04 <= (int)segUpper);
		    
		    expr t_before_04 = c.int_const("t_before_04");
		    expr t_after_04 = c.int_const("t_after_04");
		    s.add(t_before_04 >= (int)segLower + 1 && t_before_04 <= (int)segUpper && t_after_04 >= (int)segLower && t_after_04 <= (int)segUpper);
		    
		    func_decl rho_04 = function("rho_04", c.int_sort(), c.int_sort());
		    func_decl rho_primed_04 = function("rho_primed_04", c.real_sort(), c.real_sort());
		    
		    func_decl rho_40 = function("rho_40", c.int_sort(), c.int_sort());
		    func_decl rho_primed_40 = function("rho_primed_40", c.real_sort(), c.real_sort());
		    
		    expr pwl_04 = c.int_const("pwl_04");
		    s.add(pwl_04 >= (int)segLower + 1 && pwl_04 <= (int)segUpper);
		    
		    expr pwl_40 = c.int_const("pwl_40");
		    s.add(pwl_40 >= (int)segLower + 1 && pwl_40 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_04(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_04(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_40(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_40(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_04, t_after_04, implies(((t_before_04 < t_after_04) && (t_before_04 >= (int)segLower + 1) && (t_before_04 <= (int)segUpper) && (t_after_04 >= (int)segLower) && (t_after_04 <= (int)segUpper)), ((rho_04(t_before_04) < rho_04(t_after_04)) && (rho_40(t_before_04) < rho_40(t_after_04))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_4, implies(((rho_04(pred_0) == pred_4) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_0_x(pred_0)) * (a_4_x(pred_4) - a_0_x(pred_0))) + ((a_4_y(pred_4) - a_0_y(pred_0)) * (a_4_y(pred_4) - a_0_y(pred_0))) + ((a_4_z(pred_4) - a_0_z(pred_0)) * (a_4_z(pred_4) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_04, implies(((pwl_04 >= (int)segLower + 1) && (pwl_04 <= (int)segUpper)), (rho_primed_04(pwl_04) == rho_04(c.int_val(pwl_04)) + ((pwl_04 - c.int_val(pwl_04)) * (rho_04(c.int_val(pwl_04) + 1) - rho_04(c.int_val(pwl_04))))))));
			s.add(forall(pwl_40, implies(((pwl_40 >= (int)segLower + 1) && (pwl_40 <= (int)segUpper)), (rho_primed_40(pwl_40) == rho_40(c.int_val(pwl_40)) + ((pwl_40 - c.int_val(pwl_40)) * (rho_40(c.int_val(pwl_40) + 1) - rho_40(c.int_val(pwl_40))))))));
			
			//inverse re-timing
			s.add(forall(t_04, implies(((t_04 >= (int)segLower) && (t_04 <= (int)segUpper)), (rho_40(rho_04(t_04)) == t_04))));

			// ================ AGENT 0 AND AGENT 4 END ================ //
			
			// =============== AGENT 0 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_05 = c.int_const("t_05");
		    s.add(t_05 >= (int)segLower + 1 && t_05 <= (int)segUpper);
		    
		    expr t_before_05 = c.int_const("t_before_05");
		    expr t_after_05 = c.int_const("t_after_05");
		    s.add(t_before_05 >= (int)segLower + 1 && t_before_05 <= (int)segUpper && t_after_05 >= (int)segLower && t_after_05 <= (int)segUpper);
		    
		    func_decl rho_05 = function("rho_05", c.int_sort(), c.int_sort());
		    func_decl rho_primed_05 = function("rho_primed_05", c.real_sort(), c.real_sort());
		    
		    func_decl rho_50 = function("rho_50", c.int_sort(), c.int_sort());
		    func_decl rho_primed_50 = function("rho_primed_50", c.real_sort(), c.real_sort());
		    
		    expr pwl_05 = c.int_const("pwl_05");
		    s.add(pwl_05 >= (int)segLower + 1 && pwl_05 <= (int)segUpper);
		    
		    expr pwl_50 = c.int_const("pwl_50");
		    s.add(pwl_50 >= (int)segLower + 1 && pwl_50 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_05(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_05(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_50(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_50(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_05, t_after_05, implies(((t_before_05 < t_after_05) && (t_before_05 >= (int)segLower + 1) && (t_before_05 <= (int)segUpper) && (t_after_05 >= (int)segLower) && (t_after_05 <= (int)segUpper)), ((rho_05(t_before_05) < rho_05(t_after_05)) && (rho_50(t_before_05) < rho_50(t_after_05))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_5, implies(((rho_05(pred_0) == pred_5) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_0_x(pred_0)) * (a_5_x(pred_5) - a_0_x(pred_0))) + ((a_5_y(pred_5) - a_0_y(pred_0)) * (a_5_y(pred_5) - a_0_y(pred_0))) + ((a_5_z(pred_5) - a_0_z(pred_0)) * (a_5_z(pred_5) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_05, implies(((pwl_05 >= (int)segLower + 1) && (pwl_05 <= (int)segUpper)), (rho_primed_05(pwl_05) == rho_05(c.int_val(pwl_05)) + ((pwl_05 - c.int_val(pwl_05)) * (rho_05(c.int_val(pwl_05) + 1) - rho_05(c.int_val(pwl_05))))))));
			s.add(forall(pwl_50, implies(((pwl_50 >= (int)segLower + 1) && (pwl_50 <= (int)segUpper)), (rho_primed_50(pwl_50) == rho_50(c.int_val(pwl_50)) + ((pwl_50 - c.int_val(pwl_50)) * (rho_50(c.int_val(pwl_50) + 1) - rho_50(c.int_val(pwl_50))))))));
			
			//inverse re-timing
			s.add(forall(t_05, implies(((t_05 >= (int)segLower) && (t_05 <= (int)segUpper)), (rho_50(rho_05(t_05)) == t_05))));

			// ================ AGENT 0 AND AGENT 5 END ================ //
			
			// =============== AGENT 1 AND AGENT 2 START =============== //
			
			//agent pair smt variables
			expr t_12 = c.int_const("t_12");
		    s.add(t_12 >= (int)segLower + 1 && t_12 <= (int)segUpper);
		    
		    expr t_before_12 = c.int_const("t_before_12");
		    expr t_after_12 = c.int_const("t_after_12");
		    s.add(t_before_12 >= (int)segLower + 1 && t_before_12 <= (int)segUpper && t_after_12 >= (int)segLower && t_after_12 <= (int)segUpper);
		    
		    func_decl rho_12 = function("rho_12", c.int_sort(), c.int_sort());
		    func_decl rho_primed_12 = function("rho_primed_12", c.real_sort(), c.real_sort());
		    
		    func_decl rho_21 = function("rho_21", c.int_sort(), c.int_sort());
		    func_decl rho_primed_21 = function("rho_primed_21", c.real_sort(), c.real_sort());
		    
		    expr pwl_12 = c.int_const("pwl_12");
		    s.add(pwl_12 >= (int)segLower + 1 && pwl_12 <= (int)segUpper);
		    
		    expr pwl_21 = c.int_const("pwl_21");
		    s.add(pwl_21 >= (int)segLower + 1 && pwl_21 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_12(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_12(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_21(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_21(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_12, t_after_12, implies(((t_before_12 < t_after_12) && (t_before_12 >= (int)segLower + 1) && (t_before_12 <= (int)segUpper) && (t_after_12 >= (int)segLower) && (t_after_12 <= (int)segUpper)), ((rho_12(t_before_12) < rho_12(t_after_12)) && (rho_21(t_before_12) < rho_21(t_after_12))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_2, implies(((rho_12(pred_1) == pred_2) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_2 >= (int)segLower) && (pred_2 <= (int)segUpper)), (c.real_val(delta) <= (((a_2_x(pred_2) - a_1_x(pred_1)) * (a_2_x(pred_2) - a_1_x(pred_1))) + ((a_2_y(pred_2) - a_1_y(pred_1)) * (a_2_y(pred_2) - a_1_y(pred_1))) + ((a_2_z(pred_2) - a_1_z(pred_1)) * (a_2_z(pred_2) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_12, implies(((pwl_12 >= (int)segLower + 1) && (pwl_12 <= (int)segUpper)), (rho_primed_12(pwl_12) == rho_12(c.int_val(pwl_12)) + ((pwl_12 - c.int_val(pwl_12)) * (rho_12(c.int_val(pwl_12) + 1) - rho_12(c.int_val(pwl_12))))))));
			s.add(forall(pwl_21, implies(((pwl_21 >= (int)segLower + 1) && (pwl_21 <= (int)segUpper)), (rho_primed_21(pwl_21) == rho_21(c.int_val(pwl_21)) + ((pwl_21 - c.int_val(pwl_21)) * (rho_21(c.int_val(pwl_21) + 1) - rho_21(c.int_val(pwl_21))))))));
			
			//inverse re-timing
			s.add(forall(t_12, implies(((t_12 >= (int)segLower) && (t_12 <= (int)segUpper)), (rho_21(rho_12(t_12)) == t_12))));

			// ================ AGENT 1 AND AGENT 2 END ================ //
			
			// =============== AGENT 1 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_13 = c.int_const("t_13");
		    s.add(t_13 >= (int)segLower + 1 && t_13 <= (int)segUpper);
		    
		    expr t_before_13 = c.int_const("t_before_13");
		    expr t_after_13 = c.int_const("t_after_13");
		    s.add(t_before_13 >= (int)segLower + 1 && t_before_13 <= (int)segUpper && t_after_13 >= (int)segLower && t_after_13 <= (int)segUpper);
		    
		    func_decl rho_13 = function("rho_13", c.int_sort(), c.int_sort());
		    func_decl rho_primed_13 = function("rho_primed_13", c.real_sort(), c.real_sort());
		    
		    func_decl rho_31 = function("rho_31", c.int_sort(), c.int_sort());
		    func_decl rho_primed_31 = function("rho_primed_31", c.real_sort(), c.real_sort());
		    
		    expr pwl_13 = c.int_const("pwl_13");
		    s.add(pwl_13 >= (int)segLower + 1 && pwl_13 <= (int)segUpper);
		    
		    expr pwl_31 = c.int_const("pwl_31");
		    s.add(pwl_31 >= (int)segLower + 1 && pwl_31 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_13(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_13(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_31(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_31(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_13, t_after_13, implies(((t_before_13 < t_after_13) && (t_before_13 >= (int)segLower + 1) && (t_before_13 <= (int)segUpper) && (t_after_13 >= (int)segLower) && (t_after_13 <= (int)segUpper)), ((rho_13(t_before_13) < rho_13(t_after_13)) && (rho_31(t_before_13) < rho_31(t_after_13))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_3, implies(((rho_13(pred_1) == pred_3) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_1_x(pred_1)) * (a_3_x(pred_3) - a_1_x(pred_1))) + ((a_3_y(pred_3) - a_1_y(pred_1)) * (a_3_y(pred_3) - a_1_y(pred_1))) + ((a_3_z(pred_3) - a_1_z(pred_1)) * (a_3_z(pred_3) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_13, implies(((pwl_13 >= (int)segLower + 1) && (pwl_13 <= (int)segUpper)), (rho_primed_13(pwl_13) == rho_13(c.int_val(pwl_13)) + ((pwl_13 - c.int_val(pwl_13)) * (rho_13(c.int_val(pwl_13) + 1) - rho_13(c.int_val(pwl_13))))))));
			s.add(forall(pwl_31, implies(((pwl_31 >= (int)segLower + 1) && (pwl_31 <= (int)segUpper)), (rho_primed_31(pwl_31) == rho_31(c.int_val(pwl_31)) + ((pwl_31 - c.int_val(pwl_31)) * (rho_31(c.int_val(pwl_31) + 1) - rho_31(c.int_val(pwl_31))))))));
			
			//inverse re-timing
			s.add(forall(t_13, implies(((t_13 >= (int)segLower) && (t_13 <= (int)segUpper)), (rho_31(rho_13(t_13)) == t_13))));

			// ================ AGENT 1 AND AGENT 3 END ================ //
			
			// =============== AGENT 1 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_14 = c.int_const("t_14");
		    s.add(t_14 >= (int)segLower + 1 && t_14 <= (int)segUpper);
		    
		    expr t_before_14 = c.int_const("t_before_14");
		    expr t_after_14 = c.int_const("t_after_14");
		    s.add(t_before_14 >= (int)segLower + 1 && t_before_14 <= (int)segUpper && t_after_14 >= (int)segLower && t_after_14 <= (int)segUpper);
		    
		    func_decl rho_14 = function("rho_14", c.int_sort(), c.int_sort());
		    func_decl rho_primed_14 = function("rho_primed_14", c.real_sort(), c.real_sort());
		    
		    func_decl rho_41 = function("rho_41", c.int_sort(), c.int_sort());
		    func_decl rho_primed_41 = function("rho_primed_41", c.real_sort(), c.real_sort());
		    
		    expr pwl_14 = c.int_const("pwl_14");
		    s.add(pwl_14 >= (int)segLower + 1 && pwl_14 <= (int)segUpper);
		    
		    expr pwl_41 = c.int_const("pwl_41");
		    s.add(pwl_41 >= (int)segLower + 1 && pwl_41 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_14(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_14(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_41(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_41(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_14, t_after_14, implies(((t_before_14 < t_after_14) && (t_before_14 >= (int)segLower + 1) && (t_before_14 <= (int)segUpper) && (t_after_14 >= (int)segLower) && (t_after_14 <= (int)segUpper)), ((rho_14(t_before_14) < rho_14(t_after_14)) && (rho_41(t_before_14) < rho_41(t_after_14))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_4, implies(((rho_14(pred_1) == pred_4) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_1_x(pred_1)) * (a_4_x(pred_4) - a_1_x(pred_1))) + ((a_4_y(pred_4) - a_1_y(pred_1)) * (a_4_y(pred_4) - a_1_y(pred_1))) + ((a_4_z(pred_4) - a_1_z(pred_1)) * (a_4_z(pred_4) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_14, implies(((pwl_14 >= (int)segLower + 1) && (pwl_14 <= (int)segUpper)), (rho_primed_14(pwl_14) == rho_14(c.int_val(pwl_14)) + ((pwl_14 - c.int_val(pwl_14)) * (rho_14(c.int_val(pwl_14) + 1) - rho_14(c.int_val(pwl_14))))))));
			s.add(forall(pwl_41, implies(((pwl_41 >= (int)segLower + 1) && (pwl_41 <= (int)segUpper)), (rho_primed_41(pwl_41) == rho_41(c.int_val(pwl_41)) + ((pwl_41 - c.int_val(pwl_41)) * (rho_41(c.int_val(pwl_41) + 1) - rho_41(c.int_val(pwl_41))))))));
			
			//inverse re-timing
			s.add(forall(t_14, implies(((t_14 >= (int)segLower) && (t_14 <= (int)segUpper)), (rho_41(rho_14(t_14)) == t_14))));

			// ================ AGENT 1 AND AGENT 4 END ================ //
			
			// =============== AGENT 1 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_15 = c.int_const("t_15");
		    s.add(t_15 >= (int)segLower + 1 && t_15 <= (int)segUpper);
		    
		    expr t_before_15 = c.int_const("t_before_15");
		    expr t_after_15 = c.int_const("t_after_15");
		    s.add(t_before_15 >= (int)segLower + 1 && t_before_15 <= (int)segUpper && t_after_15 >= (int)segLower && t_after_15 <= (int)segUpper);
		    
		    func_decl rho_15 = function("rho_15", c.int_sort(), c.int_sort());
		    func_decl rho_primed_15 = function("rho_primed_15", c.real_sort(), c.real_sort());
		    
		    func_decl rho_51 = function("rho_51", c.int_sort(), c.int_sort());
		    func_decl rho_primed_51 = function("rho_primed_51", c.real_sort(), c.real_sort());
		    
		    expr pwl_15 = c.int_const("pwl_15");
		    s.add(pwl_15 >= (int)segLower + 1 && pwl_15 <= (int)segUpper);
		    
		    expr pwl_51 = c.int_const("pwl_51");
		    s.add(pwl_51 >= (int)segLower + 1 && pwl_51 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_15(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_15(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_51(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_51(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_15, t_after_15, implies(((t_before_15 < t_after_15) && (t_before_15 >= (int)segLower + 1) && (t_before_15 <= (int)segUpper) && (t_after_15 >= (int)segLower) && (t_after_15 <= (int)segUpper)), ((rho_15(t_before_15) < rho_15(t_after_15)) && (rho_51(t_before_15) < rho_51(t_after_15))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_5, implies(((rho_15(pred_1) == pred_5) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_1_x(pred_1)) * (a_5_x(pred_5) - a_1_x(pred_1))) + ((a_5_y(pred_5) - a_1_y(pred_1)) * (a_5_y(pred_5) - a_1_y(pred_1))) + ((a_5_z(pred_5) - a_1_z(pred_1)) * (a_5_z(pred_5) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_15, implies(((pwl_15 >= (int)segLower + 1) && (pwl_15 <= (int)segUpper)), (rho_primed_15(pwl_15) == rho_15(c.int_val(pwl_15)) + ((pwl_15 - c.int_val(pwl_15)) * (rho_15(c.int_val(pwl_15) + 1) - rho_15(c.int_val(pwl_15))))))));
			s.add(forall(pwl_51, implies(((pwl_51 >= (int)segLower + 1) && (pwl_51 <= (int)segUpper)), (rho_primed_51(pwl_51) == rho_51(c.int_val(pwl_51)) + ((pwl_51 - c.int_val(pwl_51)) * (rho_51(c.int_val(pwl_51) + 1) - rho_51(c.int_val(pwl_51))))))));
			
			//inverse re-timing
			s.add(forall(t_15, implies(((t_15 >= (int)segLower) && (t_15 <= (int)segUpper)), (rho_51(rho_15(t_15)) == t_15))));

			// ================ AGENT 1 AND AGENT 5 END ================ //
			
			// =============== AGENT 2 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_23 = c.int_const("t_23");
		    s.add(t_23 >= (int)segLower + 1 && t_23 <= (int)segUpper);
		    
		    expr t_before_23 = c.int_const("t_before_23");
		    expr t_after_23 = c.int_const("t_after_23");
		    s.add(t_before_23 >= (int)segLower + 1 && t_before_23 <= (int)segUpper && t_after_23 >= (int)segLower && t_after_23 <= (int)segUpper);
		    
		    func_decl rho_23 = function("rho_23", c.int_sort(), c.int_sort());
		    func_decl rho_primed_23 = function("rho_primed_23", c.real_sort(), c.real_sort());
		    
		    func_decl rho_32 = function("rho_32", c.int_sort(), c.int_sort());
		    func_decl rho_primed_32 = function("rho_primed_32", c.real_sort(), c.real_sort());
		    
		    expr pwl_23 = c.int_const("pwl_23");
		    s.add(pwl_23 >= (int)segLower + 1 && pwl_23 <= (int)segUpper);
		    
		    expr pwl_32 = c.int_const("pwl_32");
		    s.add(pwl_32 >= (int)segLower + 1 && pwl_32 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_23(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_23(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_32(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_32(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_23, t_after_23, implies(((t_before_23 < t_after_23) && (t_before_23 >= (int)segLower + 1) && (t_before_23 <= (int)segUpper) && (t_after_23 >= (int)segLower) && (t_after_23 <= (int)segUpper)), ((rho_23(t_before_23) < rho_23(t_after_23)) && (rho_32(t_before_23) < rho_32(t_after_23))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_3, implies(((rho_23(pred_2) == pred_3) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_2_x(pred_2)) * (a_3_x(pred_3) - a_2_x(pred_2))) + ((a_3_y(pred_3) - a_2_y(pred_2)) * (a_3_y(pred_3) - a_2_y(pred_2))) + ((a_3_z(pred_3) - a_2_z(pred_2)) * (a_3_z(pred_3) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_23, implies(((pwl_23 >= (int)segLower + 1) && (pwl_23 <= (int)segUpper)), (rho_primed_23(pwl_23) == rho_23(c.int_val(pwl_23)) + ((pwl_23 - c.int_val(pwl_23)) * (rho_23(c.int_val(pwl_23) + 1) - rho_23(c.int_val(pwl_23))))))));
			s.add(forall(pwl_32, implies(((pwl_32 >= (int)segLower + 1) && (pwl_32 <= (int)segUpper)), (rho_primed_32(pwl_32) == rho_32(c.int_val(pwl_32)) + ((pwl_32 - c.int_val(pwl_32)) * (rho_32(c.int_val(pwl_32) + 1) - rho_32(c.int_val(pwl_32))))))));
			
			//inverse re-timing
			s.add(forall(t_23, implies(((t_23 >= (int)segLower) && (t_23 <= (int)segUpper)), (rho_32(rho_23(t_23)) == t_23))));

			// ================ AGENT 2 AND AGENT 3 END ================ //
			
			// =============== AGENT 2 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_24 = c.int_const("t_24");
		    s.add(t_24 >= (int)segLower + 1 && t_24 <= (int)segUpper);
		    
		    expr t_before_24 = c.int_const("t_before_24");
		    expr t_after_24 = c.int_const("t_after_24");
		    s.add(t_before_24 >= (int)segLower + 1 && t_before_24 <= (int)segUpper && t_after_24 >= (int)segLower && t_after_24 <= (int)segUpper);
		    
		    func_decl rho_24 = function("rho_24", c.int_sort(), c.int_sort());
		    func_decl rho_primed_24 = function("rho_primed_24", c.real_sort(), c.real_sort());
		    
		    func_decl rho_42 = function("rho_42", c.int_sort(), c.int_sort());
		    func_decl rho_primed_42 = function("rho_primed_42", c.real_sort(), c.real_sort());
		    
		    expr pwl_24 = c.int_const("pwl_24");
		    s.add(pwl_24 >= (int)segLower + 1 && pwl_24 <= (int)segUpper);
		    
		    expr pwl_42 = c.int_const("pwl_42");
		    s.add(pwl_42 >= (int)segLower + 1 && pwl_42 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_24(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_24(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_42(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_42(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_24, t_after_24, implies(((t_before_24 < t_after_24) && (t_before_24 >= (int)segLower + 1) && (t_before_24 <= (int)segUpper) && (t_after_24 >= (int)segLower) && (t_after_24 <= (int)segUpper)), ((rho_24(t_before_24) < rho_24(t_after_24)) && (rho_42(t_before_24) < rho_42(t_after_24))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_4, implies(((rho_24(pred_2) == pred_4) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_2_x(pred_2)) * (a_4_x(pred_4) - a_2_x(pred_2))) + ((a_4_y(pred_4) - a_2_y(pred_2)) * (a_4_y(pred_4) - a_2_y(pred_2))) + ((a_4_z(pred_4) - a_2_z(pred_2)) * (a_4_z(pred_4) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_24, implies(((pwl_24 >= (int)segLower + 1) && (pwl_24 <= (int)segUpper)), (rho_primed_24(pwl_24) == rho_24(c.int_val(pwl_24)) + ((pwl_24 - c.int_val(pwl_24)) * (rho_24(c.int_val(pwl_24) + 1) - rho_24(c.int_val(pwl_24))))))));
			s.add(forall(pwl_42, implies(((pwl_42 >= (int)segLower + 1) && (pwl_42 <= (int)segUpper)), (rho_primed_42(pwl_42) == rho_42(c.int_val(pwl_42)) + ((pwl_42 - c.int_val(pwl_42)) * (rho_42(c.int_val(pwl_42) + 1) - rho_42(c.int_val(pwl_42))))))));
			
			//inverse re-timing
			s.add(forall(t_24, implies(((t_24 >= (int)segLower) && (t_24 <= (int)segUpper)), (rho_42(rho_24(t_24)) == t_24))));

			// ================ AGENT 2 AND AGENT 4 END ================ //
			
			// =============== AGENT 2 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_25 = c.int_const("t_25");
		    s.add(t_25 >= (int)segLower + 1 && t_25 <= (int)segUpper);
		    
		    expr t_before_25 = c.int_const("t_before_25");
		    expr t_after_25 = c.int_const("t_after_25");
		    s.add(t_before_25 >= (int)segLower + 1 && t_before_25 <= (int)segUpper && t_after_25 >= (int)segLower && t_after_25 <= (int)segUpper);
		    
		    func_decl rho_25 = function("rho_25", c.int_sort(), c.int_sort());
		    func_decl rho_primed_25 = function("rho_primed_25", c.real_sort(), c.real_sort());
		    
		    func_decl rho_52 = function("rho_52", c.int_sort(), c.int_sort());
		    func_decl rho_primed_52 = function("rho_primed_52", c.real_sort(), c.real_sort());
		    
		    expr pwl_25 = c.int_const("pwl_25");
		    s.add(pwl_25 >= (int)segLower + 1 && pwl_25 <= (int)segUpper);
		    
		    expr pwl_52 = c.int_const("pwl_52");
		    s.add(pwl_52 >= (int)segLower + 1 && pwl_52 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_25(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_25(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_52(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_52(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_25, t_after_25, implies(((t_before_25 < t_after_25) && (t_before_25 >= (int)segLower + 1) && (t_before_25 <= (int)segUpper) && (t_after_25 >= (int)segLower) && (t_after_25 <= (int)segUpper)), ((rho_25(t_before_25) < rho_25(t_after_25)) && (rho_52(t_before_25) < rho_52(t_after_25))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_5, implies(((rho_25(pred_2) == pred_5) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_2_x(pred_2)) * (a_5_x(pred_5) - a_2_x(pred_2))) + ((a_5_y(pred_5) - a_2_y(pred_2)) * (a_5_y(pred_5) - a_2_y(pred_2))) + ((a_5_z(pred_5) - a_2_z(pred_2)) * (a_5_z(pred_5) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_25, implies(((pwl_25 >= (int)segLower + 1) && (pwl_25 <= (int)segUpper)), (rho_primed_25(pwl_25) == rho_25(c.int_val(pwl_25)) + ((pwl_25 - c.int_val(pwl_25)) * (rho_25(c.int_val(pwl_25) + 1) - rho_25(c.int_val(pwl_25))))))));
			s.add(forall(pwl_52, implies(((pwl_52 >= (int)segLower + 1) && (pwl_52 <= (int)segUpper)), (rho_primed_52(pwl_52) == rho_52(c.int_val(pwl_52)) + ((pwl_52 - c.int_val(pwl_52)) * (rho_52(c.int_val(pwl_52) + 1) - rho_52(c.int_val(pwl_52))))))));
			
			//inverse re-timing
			s.add(forall(t_25, implies(((t_25 >= (int)segLower) && (t_25 <= (int)segUpper)), (rho_52(rho_25(t_25)) == t_25))));

			// ================ AGENT 2 AND AGENT 5 END ================ //
			
			// =============== AGENT 3 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_34 = c.int_const("t_34");
		    s.add(t_34 >= (int)segLower + 1 && t_34 <= (int)segUpper);
		    
		    expr t_before_34 = c.int_const("t_before_34");
		    expr t_after_34 = c.int_const("t_after_34");
		    s.add(t_before_34 >= (int)segLower + 1 && t_before_34 <= (int)segUpper && t_after_34 >= (int)segLower && t_after_34 <= (int)segUpper);
		    
		    func_decl rho_34 = function("rho_34", c.int_sort(), c.int_sort());
		    func_decl rho_primed_34 = function("rho_primed_34", c.real_sort(), c.real_sort());
		    
		    func_decl rho_43 = function("rho_43", c.int_sort(), c.int_sort());
		    func_decl rho_primed_43 = function("rho_primed_43", c.real_sort(), c.real_sort());
		    
		    expr pwl_34 = c.int_const("pwl_34");
		    s.add(pwl_34 >= (int)segLower + 1 && pwl_34 <= (int)segUpper);
		    
		    expr pwl_43 = c.int_const("pwl_43");
		    s.add(pwl_43 >= (int)segLower + 1 && pwl_43 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_34(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_34(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_43(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_43(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_34, t_after_34, implies(((t_before_34 < t_after_34) && (t_before_34 >= (int)segLower + 1) && (t_before_34 <= (int)segUpper) && (t_after_34 >= (int)segLower) && (t_after_34 <= (int)segUpper)), ((rho_34(t_before_34) < rho_34(t_after_34)) && (rho_43(t_before_34) < rho_43(t_after_34))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_4, implies(((rho_34(pred_3) == pred_4) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_3_x(pred_3)) * (a_4_x(pred_4) - a_3_x(pred_3))) + ((a_4_y(pred_4) - a_3_y(pred_3)) * (a_4_y(pred_4) - a_3_y(pred_3))) + ((a_4_z(pred_4) - a_3_z(pred_3)) * (a_4_z(pred_4) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_34, implies(((pwl_34 >= (int)segLower + 1) && (pwl_34 <= (int)segUpper)), (rho_primed_34(pwl_34) == rho_34(c.int_val(pwl_34)) + ((pwl_34 - c.int_val(pwl_34)) * (rho_34(c.int_val(pwl_34) + 1) - rho_34(c.int_val(pwl_34))))))));
			s.add(forall(pwl_43, implies(((pwl_43 >= (int)segLower + 1) && (pwl_43 <= (int)segUpper)), (rho_primed_43(pwl_43) == rho_43(c.int_val(pwl_43)) + ((pwl_43 - c.int_val(pwl_43)) * (rho_43(c.int_val(pwl_43) + 1) - rho_43(c.int_val(pwl_43))))))));
			
			//inverse re-timing
			s.add(forall(t_34, implies(((t_34 >= (int)segLower) && (t_34 <= (int)segUpper)), (rho_43(rho_34(t_34)) == t_34))));

			// ================ AGENT 3 AND AGENT 4 END ================ //
			
			// =============== AGENT 3 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_35 = c.int_const("t_35");
		    s.add(t_35 >= (int)segLower + 1 && t_35 <= (int)segUpper);
		    
		    expr t_before_35 = c.int_const("t_before_35");
		    expr t_after_35 = c.int_const("t_after_35");
		    s.add(t_before_35 >= (int)segLower + 1 && t_before_35 <= (int)segUpper && t_after_35 >= (int)segLower && t_after_35 <= (int)segUpper);
		    
		    func_decl rho_35 = function("rho_35", c.int_sort(), c.int_sort());
		    func_decl rho_primed_35 = function("rho_primed_35", c.real_sort(), c.real_sort());
		    
		    func_decl rho_53 = function("rho_53", c.int_sort(), c.int_sort());
		    func_decl rho_primed_53 = function("rho_primed_53", c.real_sort(), c.real_sort());
		    
		    expr pwl_35 = c.int_const("pwl_35");
		    s.add(pwl_35 >= (int)segLower + 1 && pwl_35 <= (int)segUpper);
		    
		    expr pwl_53 = c.int_const("pwl_53");
		    s.add(pwl_53 >= (int)segLower + 1 && pwl_53 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_35(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_35(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_53(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_53(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_35, t_after_35, implies(((t_before_35 < t_after_35) && (t_before_35 >= (int)segLower + 1) && (t_before_35 <= (int)segUpper) && (t_after_35 >= (int)segLower) && (t_after_35 <= (int)segUpper)), ((rho_35(t_before_35) < rho_35(t_after_35)) && (rho_53(t_before_35) < rho_53(t_after_35))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_5, implies(((rho_35(pred_3) == pred_5) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_3_x(pred_3)) * (a_5_x(pred_5) - a_3_x(pred_3))) + ((a_5_y(pred_5) - a_3_y(pred_3)) * (a_5_y(pred_5) - a_3_y(pred_3))) + ((a_5_z(pred_5) - a_3_z(pred_3)) * (a_5_z(pred_5) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_35, implies(((pwl_35 >= (int)segLower + 1) && (pwl_35 <= (int)segUpper)), (rho_primed_35(pwl_35) == rho_35(c.int_val(pwl_35)) + ((pwl_35 - c.int_val(pwl_35)) * (rho_35(c.int_val(pwl_35) + 1) - rho_35(c.int_val(pwl_35))))))));
			s.add(forall(pwl_53, implies(((pwl_53 >= (int)segLower + 1) && (pwl_53 <= (int)segUpper)), (rho_primed_53(pwl_53) == rho_53(c.int_val(pwl_53)) + ((pwl_53 - c.int_val(pwl_53)) * (rho_53(c.int_val(pwl_53) + 1) - rho_53(c.int_val(pwl_53))))))));
			
			//inverse re-timing
			s.add(forall(t_35, implies(((t_35 >= (int)segLower) && (t_35 <= (int)segUpper)), (rho_53(rho_35(t_35)) == t_35))));

			// ================ AGENT 3 AND AGENT 5 END ================ //
			
			// =============== AGENT 4 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_45 = c.int_const("t_45");
		    s.add(t_45 >= (int)segLower + 1 && t_45 <= (int)segUpper);
		    
		    expr t_before_45 = c.int_const("t_before_45");
		    expr t_after_45 = c.int_const("t_after_45");
		    s.add(t_before_45 >= (int)segLower + 1 && t_before_45 <= (int)segUpper && t_after_45 >= (int)segLower && t_after_45 <= (int)segUpper);
		    
		    func_decl rho_45 = function("rho_45", c.int_sort(), c.int_sort());
		    func_decl rho_primed_45 = function("rho_primed_45", c.real_sort(), c.real_sort());
		    
		    func_decl rho_54 = function("rho_54", c.int_sort(), c.int_sort());
		    func_decl rho_primed_54 = function("rho_primed_54", c.real_sort(), c.real_sort());
		    
		    expr pwl_45 = c.int_const("pwl_45");
		    s.add(pwl_45 >= (int)segLower + 1 && pwl_45 <= (int)segUpper);
		    
		    expr pwl_54 = c.int_const("pwl_54");
		    s.add(pwl_54 >= (int)segLower + 1 && pwl_54 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_45(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_45(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_54(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_54(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_45, t_after_45, implies(((t_before_45 < t_after_45) && (t_before_45 >= (int)segLower + 1) && (t_before_45 <= (int)segUpper) && (t_after_45 >= (int)segLower) && (t_after_45 <= (int)segUpper)), ((rho_45(t_before_45) < rho_45(t_after_45)) && (rho_54(t_before_45) < rho_54(t_after_45))))));
			
			//mutual separation constraint
			s.add(forall(pred_4, pred_5, implies(((rho_45(pred_4) == pred_5) && (pred_4 >= (int)segLower + 1) && (pred_4 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_4_x(pred_4)) * (a_5_x(pred_5) - a_4_x(pred_4))) + ((a_5_y(pred_5) - a_4_y(pred_4)) * (a_5_y(pred_5) - a_4_y(pred_4))) + ((a_5_z(pred_5) - a_4_z(pred_4)) * (a_5_z(pred_5) - a_4_z(pred_4))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_45, implies(((pwl_45 >= (int)segLower + 1) && (pwl_45 <= (int)segUpper)), (rho_primed_45(pwl_45) == rho_45(c.int_val(pwl_45)) + ((pwl_45 - c.int_val(pwl_45)) * (rho_45(c.int_val(pwl_45) + 1) - rho_45(c.int_val(pwl_45))))))));
			s.add(forall(pwl_54, implies(((pwl_54 >= (int)segLower + 1) && (pwl_54 <= (int)segUpper)), (rho_primed_54(pwl_54) == rho_54(c.int_val(pwl_54)) + ((pwl_54 - c.int_val(pwl_54)) * (rho_54(c.int_val(pwl_54) + 1) - rho_54(c.int_val(pwl_54))))))));
			
			//inverse re-timing
			s.add(forall(t_45, implies(((t_45 >= (int)segLower) && (t_45 <= (int)segUpper)), (rho_54(rho_45(t_45)) == t_45))));

			// ================ AGENT 4 AND AGENT 5 END ================ //
			
			if(s.check() == sat)
		    {
		    	std::string verdict = std::to_string(i) + " : Sat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    else
		    {
		    	std::string verdict = std::to_string(i) + " : Unsat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    
		    //reset solver
		    //s.reset();
		    
		    //build and show model
		    //model m = s.get_model();
    		//std::cout << m << "\n";
	    }
	}
	//return verdicts;
}

void runSolver_7(double eps, int segCount, double sigDur, int msgLim)
{
	//enable parallel mode
	//set_param("parallel.enable", true);
	
	//get data
	std::vector<std::vector<std::string>> agentData_0 = getData("agent_0.txt");
	std::vector<std::vector<std::string>> agentData_1 = getData("agent_1.txt");
	std::vector<std::vector<std::string>> agentData_2 = getData("agent_2.txt");
	std::vector<std::vector<std::string>> agentData_3 = getData("agent_3.txt");
	std::vector<std::vector<std::string>> agentData_4 = getData("agent_4.txt");
	std::vector<std::vector<std::string>> agentData_5 = getData("agent_5.txt");
	std::vector<std::vector<std::string>> agentData_6 = getData("agent_6.txt");
	
	//safety checks
	if(!(std::stod(agentData_0[0][0]) == 0 && std::stod(agentData_1[0][0]) == 0))
	{
		return;
	}
	
	if(std::stod(agentData_0[1][0]) != std::stod(agentData_1[1][0]))
	{
		return;
	}
	
	//second time-stamp on agent that is to be re-timed
	double t1 = std::stod(agentData_0[1][0]);
	
	//delta
	int delta = 0;
	
	//segment duration
	double segDur = sigDur / segCount;
	
	//check if the segment duration is smaller than the sampling period
	if(segDur < t1)
	{
		segCount = sigDur / t1;
	}
	
	//multiplier for normalization
	double mult = 1 / t1;
	
	//normalization of paramters
	eps *= mult;
	sigDur *= mult;
	segDur *= mult;
	
	//verdict vector
	std::vector<std::string> verdicts;
	
	#pragma omp parallel
	{
		#pragma omp for
		for(int i = 0; i < segCount; i++) 
	    {			
			//segment bounds
			double segLower = (i * segDur) - eps;
			double segUpper = (i + 1) * segDur;
			
		    context c;

		    //solver
		    solver s(c);
		    
		    //co-ord functions
		    func_decl a_0_x = function("a_0_x", c.int_sort(), c.real_sort());
		    func_decl a_0_y = function("a_0_y", c.int_sort(), c.real_sort());
		    func_decl a_0_z = function("a_0_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_1_x = function("a_1_x", c.int_sort(), c.real_sort());
		    func_decl a_1_y = function("a_1_y", c.int_sort(), c.real_sort());
		    func_decl a_1_z = function("a_1_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_2_x = function("a_2_x", c.int_sort(), c.real_sort());
		    func_decl a_2_y = function("a_2_y", c.int_sort(), c.real_sort());
		    func_decl a_2_z = function("a_2_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_3_x = function("a_3_x", c.int_sort(), c.real_sort());
		    func_decl a_3_y = function("a_3_y", c.int_sort(), c.real_sort());
		    func_decl a_3_z = function("a_3_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_4_x = function("a_4_x", c.int_sort(), c.real_sort());
		    func_decl a_4_y = function("a_4_y", c.int_sort(), c.real_sort());
		    func_decl a_4_z = function("a_4_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_5_x = function("a_5_x", c.int_sort(), c.real_sort());
		    func_decl a_5_y = function("a_5_y", c.int_sort(), c.real_sort());
		    func_decl a_5_z = function("a_5_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_6_x = function("a_6_x", c.int_sort(), c.real_sort());
		    func_decl a_6_y = function("a_6_y", c.int_sort(), c.real_sort());
		    func_decl a_6_z = function("a_6_z", c.int_sort(), c.real_sort());
		    
		    //populate co-ord functions
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_0.size())
		        {
		        	s.add(a_0_x(j) == c.real_val(agentData_0[j][1].c_str()));
		        	s.add(a_0_y(j) == c.real_val(agentData_0[j][2].c_str()));
		        	s.add(a_0_z(j) == c.real_val(agentData_0[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_1.size())
		        {
		        	s.add(a_1_x(j) == c.real_val(agentData_1[j][1].c_str()));
		        	s.add(a_1_y(j) == c.real_val(agentData_1[j][2].c_str()));
		        	s.add(a_1_z(j) == c.real_val(agentData_1[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_2.size())
		        {
		        	s.add(a_2_x(j) == c.real_val(agentData_2[j][1].c_str()));
		        	s.add(a_2_y(j) == c.real_val(agentData_2[j][2].c_str()));
		        	s.add(a_2_z(j) == c.real_val(agentData_2[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_3.size())
		        {
		        	s.add(a_3_x(j) == c.real_val(agentData_3[j][1].c_str()));
		        	s.add(a_3_y(j) == c.real_val(agentData_3[j][2].c_str()));
		        	s.add(a_3_z(j) == c.real_val(agentData_3[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_4.size())
		        {
		        	s.add(a_4_x(j) == c.real_val(agentData_4[j][1].c_str()));
		        	s.add(a_4_y(j) == c.real_val(agentData_4[j][2].c_str()));
		        	s.add(a_4_z(j) == c.real_val(agentData_4[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_5.size())
		        {
		        	s.add(a_5_x(j) == c.real_val(agentData_5[j][1].c_str()));
		        	s.add(a_5_y(j) == c.real_val(agentData_5[j][2].c_str()));
		        	s.add(a_5_z(j) == c.real_val(agentData_5[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_6.size())
		        {
		        	s.add(a_6_x(j) == c.real_val(agentData_6[j][1].c_str()));
		        	s.add(a_6_y(j) == c.real_val(agentData_6[j][2].c_str()));
		        	s.add(a_6_z(j) == c.real_val(agentData_6[j][3].c_str()));
				}
		    }
		    
		    //general smt variables		  
			expr pred_0 = c.int_const("pred_0");
			s.add(pred_0 >= (int)segLower + 1 && pred_0 <= (int)segUpper);
			
		    expr pred_1 = c.int_const("pred_1");
		    s.add(pred_1 >= (int)segLower + 1 && pred_1 <= (int)segUpper);
		    
		    expr pred_2 = c.int_const("pred_2");
		    s.add(pred_2 >= (int)segLower + 1 && pred_2 <= (int)segUpper);
		    
		    expr pred_3 = c.int_const("pred_3");
		    s.add(pred_3 >= (int)segLower + 1 && pred_3 <= (int)segUpper);
		    
		    expr pred_4 = c.int_const("pred_4");
		    s.add(pred_4 >= (int)segLower + 1 && pred_4 <= (int)segUpper);
		    
		    expr pred_5 = c.int_const("pred_5");
		    s.add(pred_5 >= (int)segLower + 1 && pred_5 <= (int)segUpper);
		    
		    expr pred_6 = c.int_const("pred_6");
		    s.add(pred_6 >= (int)segLower + 1 && pred_6 <= (int)segUpper);
		    
		    // =============== AGENT 0 AND AGENT 1 START =============== //
			
			//agent pair smt variables
			expr t_01 = c.int_const("t_01");
		    s.add(t_01 >= (int)segLower + 1 && t_01 <= (int)segUpper);
		    
		    expr t_before_01 = c.int_const("t_before_01");
		    expr t_after_01 = c.int_const("t_after_01");
		    s.add(t_before_01 >= (int)segLower + 1 && t_before_01 <= (int)segUpper && t_after_01 >= (int)segLower && t_after_01 <= (int)segUpper);
		    
		    func_decl rho_01 = function("rho_01", c.int_sort(), c.int_sort());
		    func_decl rho_primed_01 = function("rho_primed_01", c.real_sort(), c.real_sort());
		    
		    func_decl rho_10 = function("rho_10", c.int_sort(), c.int_sort());
		    func_decl rho_primed_10 = function("rho_primed_10", c.real_sort(), c.real_sort());
		    
		    expr pwl_01 = c.int_const("pwl_01");
		    s.add(pwl_01 >= (int)segLower + 1 && pwl_01 <= (int)segUpper);
		    
		    expr pwl_10 = c.int_const("pwl_10");
		    s.add(pwl_10 >= (int)segLower + 1 && pwl_10 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_01, t_after_01, implies(((t_before_01 < t_after_01) && (t_before_01 >= (int)segLower + 1) && (t_before_01 <= (int)segUpper) && (t_after_01 >= (int)segLower) && (t_after_01 <= (int)segUpper)), ((rho_01(t_before_01) < rho_01(t_after_01)) && (rho_10(t_before_01) < rho_10(t_after_01))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_1, implies(((rho_01(pred_0) == pred_1) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_1 >= (int)segLower) && (pred_1 <= (int)segUpper)), (c.real_val(delta) <= (((a_1_x(pred_1) - a_0_x(pred_0)) * (a_1_x(pred_1) - a_0_x(pred_0))) + ((a_1_y(pred_1) - a_0_y(pred_0)) * (a_1_y(pred_1) - a_0_y(pred_0))) + ((a_1_z(pred_1) - a_0_z(pred_0)) * (a_1_z(pred_1) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_01, implies(((pwl_01 >= (int)segLower + 1) && (pwl_01 <= (int)segUpper)), (rho_primed_01(pwl_01) == rho_01(c.int_val(pwl_01)) + ((pwl_01 - c.int_val(pwl_01)) * (rho_01(c.int_val(pwl_01) + 1) - rho_01(c.int_val(pwl_01))))))));
			s.add(forall(pwl_10, implies(((pwl_10 >= (int)segLower + 1) && (pwl_10 <= (int)segUpper)), (rho_primed_10(pwl_10) == rho_10(c.int_val(pwl_10)) + ((pwl_10 - c.int_val(pwl_10)) * (rho_10(c.int_val(pwl_10) + 1) - rho_10(c.int_val(pwl_10))))))));
			
			//inverse re-timing
			s.add(forall(t_01, implies(((t_01 >= (int)segLower) && (t_01 <= (int)segUpper)), (rho_10(rho_01(t_01)) == t_01))));

			// ================ AGENT 0 AND AGENT 1 END ================ //
			
			// =============== AGENT 0 AND AGENT 2 START =============== //
			
			//agent pair smt variables
			expr t_02 = c.int_const("t_02");
		    s.add(t_02 >= (int)segLower + 1 && t_02 <= (int)segUpper);
		    
		    expr t_before_02 = c.int_const("t_before_02");
		    expr t_after_02 = c.int_const("t_after_02");
		    s.add(t_before_02 >= (int)segLower + 1 && t_before_02 <= (int)segUpper && t_after_02 >= (int)segLower && t_after_02 <= (int)segUpper);
		    
		    func_decl rho_02 = function("rho_02", c.int_sort(), c.int_sort());
		    func_decl rho_primed_02 = function("rho_primed_02", c.real_sort(), c.real_sort());
		    
		    func_decl rho_20 = function("rho_20", c.int_sort(), c.int_sort());
		    func_decl rho_primed_20 = function("rho_primed_20", c.real_sort(), c.real_sort());
		    
		    expr pwl_02 = c.int_const("pwl_02");
		    s.add(pwl_02 >= (int)segLower + 1 && pwl_02 <= (int)segUpper);
		    
		    expr pwl_20 = c.int_const("pwl_20");
		    s.add(pwl_20 >= (int)segLower + 1 && pwl_20 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_02(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_02(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_20(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_20(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_02, t_after_02, implies(((t_before_02 < t_after_02) && (t_before_02 >= (int)segLower + 1) && (t_before_02 <= (int)segUpper) && (t_after_02 >= (int)segLower) && (t_after_02 <= (int)segUpper)), ((rho_02(t_before_02) < rho_02(t_after_02)) && (rho_20(t_before_02) < rho_20(t_after_02))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_2, implies(((rho_02(pred_0) == pred_2) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_2 >= (int)segLower) && (pred_2 <= (int)segUpper)), (c.real_val(delta) <= (((a_2_x(pred_2) - a_0_x(pred_0)) * (a_2_x(pred_2) - a_0_x(pred_0))) + ((a_2_y(pred_2) - a_0_y(pred_0)) * (a_2_y(pred_2) - a_0_y(pred_0))) + ((a_2_z(pred_2) - a_0_z(pred_0)) * (a_2_z(pred_2) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_02, implies(((pwl_02 >= (int)segLower + 1) && (pwl_02 <= (int)segUpper)), (rho_primed_02(pwl_02) == rho_02(c.int_val(pwl_02)) + ((pwl_02 - c.int_val(pwl_02)) * (rho_02(c.int_val(pwl_02) + 1) - rho_02(c.int_val(pwl_02))))))));
			s.add(forall(pwl_20, implies(((pwl_20 >= (int)segLower + 1) && (pwl_20 <= (int)segUpper)), (rho_primed_20(pwl_20) == rho_20(c.int_val(pwl_20)) + ((pwl_20 - c.int_val(pwl_20)) * (rho_20(c.int_val(pwl_20) + 1) - rho_20(c.int_val(pwl_20))))))));
			
			//inverse re-timing
			s.add(forall(t_02, implies(((t_02 >= (int)segLower) && (t_02 <= (int)segUpper)), (rho_20(rho_02(t_02)) == t_02))));

			// ================ AGENT 0 AND AGENT 2 END ================ //
			
			// =============== AGENT 0 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_03 = c.int_const("t_03");
		    s.add(t_03 >= (int)segLower + 1 && t_03 <= (int)segUpper);
		    
		    expr t_before_03 = c.int_const("t_before_03");
		    expr t_after_03 = c.int_const("t_after_03");
		    s.add(t_before_03 >= (int)segLower + 1 && t_before_03 <= (int)segUpper && t_after_03 >= (int)segLower && t_after_03 <= (int)segUpper);
		    
		    func_decl rho_03 = function("rho_03", c.int_sort(), c.int_sort());
		    func_decl rho_primed_03 = function("rho_primed_03", c.real_sort(), c.real_sort());
		    
		    func_decl rho_30 = function("rho_30", c.int_sort(), c.int_sort());
		    func_decl rho_primed_30 = function("rho_primed_30", c.real_sort(), c.real_sort());
		    
		    expr pwl_03 = c.int_const("pwl_03");
		    s.add(pwl_03 >= (int)segLower + 1 && pwl_03 <= (int)segUpper);
		    
		    expr pwl_30 = c.int_const("pwl_30");
		    s.add(pwl_30 >= (int)segLower + 1 && pwl_30 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_03(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_03(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_30(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_30(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_03, t_after_03, implies(((t_before_03 < t_after_03) && (t_before_03 >= (int)segLower + 1) && (t_before_03 <= (int)segUpper) && (t_after_03 >= (int)segLower) && (t_after_03 <= (int)segUpper)), ((rho_03(t_before_03) < rho_03(t_after_03)) && (rho_30(t_before_03) < rho_30(t_after_03))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_3, implies(((rho_03(pred_0) == pred_3) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_0_x(pred_0)) * (a_3_x(pred_3) - a_0_x(pred_0))) + ((a_3_y(pred_3) - a_0_y(pred_0)) * (a_3_y(pred_3) - a_0_y(pred_0))) + ((a_3_z(pred_3) - a_0_z(pred_0)) * (a_3_z(pred_3) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_03, implies(((pwl_03 >= (int)segLower + 1) && (pwl_03 <= (int)segUpper)), (rho_primed_03(pwl_03) == rho_03(c.int_val(pwl_03)) + ((pwl_03 - c.int_val(pwl_03)) * (rho_03(c.int_val(pwl_03) + 1) - rho_03(c.int_val(pwl_03))))))));
			s.add(forall(pwl_30, implies(((pwl_30 >= (int)segLower + 1) && (pwl_30 <= (int)segUpper)), (rho_primed_30(pwl_30) == rho_30(c.int_val(pwl_30)) + ((pwl_30 - c.int_val(pwl_30)) * (rho_30(c.int_val(pwl_30) + 1) - rho_30(c.int_val(pwl_30))))))));
			
			//inverse re-timing
			s.add(forall(t_03, implies(((t_03 >= (int)segLower) && (t_03 <= (int)segUpper)), (rho_30(rho_03(t_03)) == t_03))));

			// ================ AGENT 0 AND AGENT 3 END ================ //
			
			// =============== AGENT 0 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_04 = c.int_const("t_04");
		    s.add(t_04 >= (int)segLower + 1 && t_04 <= (int)segUpper);
		    
		    expr t_before_04 = c.int_const("t_before_04");
		    expr t_after_04 = c.int_const("t_after_04");
		    s.add(t_before_04 >= (int)segLower + 1 && t_before_04 <= (int)segUpper && t_after_04 >= (int)segLower && t_after_04 <= (int)segUpper);
		    
		    func_decl rho_04 = function("rho_04", c.int_sort(), c.int_sort());
		    func_decl rho_primed_04 = function("rho_primed_04", c.real_sort(), c.real_sort());
		    
		    func_decl rho_40 = function("rho_40", c.int_sort(), c.int_sort());
		    func_decl rho_primed_40 = function("rho_primed_40", c.real_sort(), c.real_sort());
		    
		    expr pwl_04 = c.int_const("pwl_04");
		    s.add(pwl_04 >= (int)segLower + 1 && pwl_04 <= (int)segUpper);
		    
		    expr pwl_40 = c.int_const("pwl_40");
		    s.add(pwl_40 >= (int)segLower + 1 && pwl_40 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_04(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_04(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_40(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_40(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_04, t_after_04, implies(((t_before_04 < t_after_04) && (t_before_04 >= (int)segLower + 1) && (t_before_04 <= (int)segUpper) && (t_after_04 >= (int)segLower) && (t_after_04 <= (int)segUpper)), ((rho_04(t_before_04) < rho_04(t_after_04)) && (rho_40(t_before_04) < rho_40(t_after_04))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_4, implies(((rho_04(pred_0) == pred_4) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_0_x(pred_0)) * (a_4_x(pred_4) - a_0_x(pred_0))) + ((a_4_y(pred_4) - a_0_y(pred_0)) * (a_4_y(pred_4) - a_0_y(pred_0))) + ((a_4_z(pred_4) - a_0_z(pred_0)) * (a_4_z(pred_4) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_04, implies(((pwl_04 >= (int)segLower + 1) && (pwl_04 <= (int)segUpper)), (rho_primed_04(pwl_04) == rho_04(c.int_val(pwl_04)) + ((pwl_04 - c.int_val(pwl_04)) * (rho_04(c.int_val(pwl_04) + 1) - rho_04(c.int_val(pwl_04))))))));
			s.add(forall(pwl_40, implies(((pwl_40 >= (int)segLower + 1) && (pwl_40 <= (int)segUpper)), (rho_primed_40(pwl_40) == rho_40(c.int_val(pwl_40)) + ((pwl_40 - c.int_val(pwl_40)) * (rho_40(c.int_val(pwl_40) + 1) - rho_40(c.int_val(pwl_40))))))));
			
			//inverse re-timing
			s.add(forall(t_04, implies(((t_04 >= (int)segLower) && (t_04 <= (int)segUpper)), (rho_40(rho_04(t_04)) == t_04))));

			// ================ AGENT 0 AND AGENT 4 END ================ //
			
			// =============== AGENT 0 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_05 = c.int_const("t_05");
		    s.add(t_05 >= (int)segLower + 1 && t_05 <= (int)segUpper);
		    
		    expr t_before_05 = c.int_const("t_before_05");
		    expr t_after_05 = c.int_const("t_after_05");
		    s.add(t_before_05 >= (int)segLower + 1 && t_before_05 <= (int)segUpper && t_after_05 >= (int)segLower && t_after_05 <= (int)segUpper);
		    
		    func_decl rho_05 = function("rho_05", c.int_sort(), c.int_sort());
		    func_decl rho_primed_05 = function("rho_primed_05", c.real_sort(), c.real_sort());
		    
		    func_decl rho_50 = function("rho_50", c.int_sort(), c.int_sort());
		    func_decl rho_primed_50 = function("rho_primed_50", c.real_sort(), c.real_sort());
		    
		    expr pwl_05 = c.int_const("pwl_05");
		    s.add(pwl_05 >= (int)segLower + 1 && pwl_05 <= (int)segUpper);
		    
		    expr pwl_50 = c.int_const("pwl_50");
		    s.add(pwl_50 >= (int)segLower + 1 && pwl_50 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_05(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_05(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_50(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_50(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_05, t_after_05, implies(((t_before_05 < t_after_05) && (t_before_05 >= (int)segLower + 1) && (t_before_05 <= (int)segUpper) && (t_after_05 >= (int)segLower) && (t_after_05 <= (int)segUpper)), ((rho_05(t_before_05) < rho_05(t_after_05)) && (rho_50(t_before_05) < rho_50(t_after_05))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_5, implies(((rho_05(pred_0) == pred_5) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_0_x(pred_0)) * (a_5_x(pred_5) - a_0_x(pred_0))) + ((a_5_y(pred_5) - a_0_y(pred_0)) * (a_5_y(pred_5) - a_0_y(pred_0))) + ((a_5_z(pred_5) - a_0_z(pred_0)) * (a_5_z(pred_5) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_05, implies(((pwl_05 >= (int)segLower + 1) && (pwl_05 <= (int)segUpper)), (rho_primed_05(pwl_05) == rho_05(c.int_val(pwl_05)) + ((pwl_05 - c.int_val(pwl_05)) * (rho_05(c.int_val(pwl_05) + 1) - rho_05(c.int_val(pwl_05))))))));
			s.add(forall(pwl_50, implies(((pwl_50 >= (int)segLower + 1) && (pwl_50 <= (int)segUpper)), (rho_primed_50(pwl_50) == rho_50(c.int_val(pwl_50)) + ((pwl_50 - c.int_val(pwl_50)) * (rho_50(c.int_val(pwl_50) + 1) - rho_50(c.int_val(pwl_50))))))));
			
			//inverse re-timing
			s.add(forall(t_05, implies(((t_05 >= (int)segLower) && (t_05 <= (int)segUpper)), (rho_50(rho_05(t_05)) == t_05))));

			// ================ AGENT 0 AND AGENT 5 END ================ //
			
			// =============== AGENT 0 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_06 = c.int_const("t_06");
		    s.add(t_06 >= (int)segLower + 1 && t_06 <= (int)segUpper);
		    
		    expr t_before_06 = c.int_const("t_before_06");
		    expr t_after_06 = c.int_const("t_after_06");
		    s.add(t_before_06 >= (int)segLower + 1 && t_before_06 <= (int)segUpper && t_after_06 >= (int)segLower && t_after_06 <= (int)segUpper);
		    
		    func_decl rho_06 = function("rho_06", c.int_sort(), c.int_sort());
		    func_decl rho_primed_06 = function("rho_primed_06", c.real_sort(), c.real_sort());
		    
		    func_decl rho_60 = function("rho_60", c.int_sort(), c.int_sort());
		    func_decl rho_primed_60 = function("rho_primed_60", c.real_sort(), c.real_sort());
		    
		    expr pwl_06 = c.int_const("pwl_06");
		    s.add(pwl_06 >= (int)segLower + 1 && pwl_06 <= (int)segUpper);
		    
		    expr pwl_60 = c.int_const("pwl_60");
		    s.add(pwl_60 >= (int)segLower + 1 && pwl_60 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_06(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_06(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_60(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_60(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_06, t_after_06, implies(((t_before_06 < t_after_06) && (t_before_06 >= (int)segLower + 1) && (t_before_06 <= (int)segUpper) && (t_after_06 >= (int)segLower) && (t_after_06 <= (int)segUpper)), ((rho_06(t_before_06) < rho_06(t_after_06)) && (rho_60(t_before_06) < rho_60(t_after_06))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_6, implies(((rho_06(pred_0) == pred_6) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_0_x(pred_0)) * (a_6_x(pred_6) - a_0_x(pred_0))) + ((a_6_y(pred_6) - a_0_y(pred_0)) * (a_6_y(pred_6) - a_0_y(pred_0))) + ((a_6_z(pred_6) - a_0_z(pred_0)) * (a_6_z(pred_6) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_06, implies(((pwl_06 >= (int)segLower + 1) && (pwl_06 <= (int)segUpper)), (rho_primed_06(pwl_06) == rho_06(c.int_val(pwl_06)) + ((pwl_06 - c.int_val(pwl_06)) * (rho_06(c.int_val(pwl_06) + 1) - rho_06(c.int_val(pwl_06))))))));
			s.add(forall(pwl_60, implies(((pwl_60 >= (int)segLower + 1) && (pwl_60 <= (int)segUpper)), (rho_primed_60(pwl_60) == rho_60(c.int_val(pwl_60)) + ((pwl_60 - c.int_val(pwl_60)) * (rho_60(c.int_val(pwl_60) + 1) - rho_60(c.int_val(pwl_60))))))));
			
			//inverse re-timing
			s.add(forall(t_06, implies(((t_06 >= (int)segLower) && (t_06 <= (int)segUpper)), (rho_60(rho_06(t_06)) == t_06))));

			// ================ AGENT 0 AND AGENT 6 END ================ //
			
			// =============== AGENT 1 AND AGENT 2 START =============== //
			
			//agent pair smt variables
			expr t_12 = c.int_const("t_12");
		    s.add(t_12 >= (int)segLower + 1 && t_12 <= (int)segUpper);
		    
		    expr t_before_12 = c.int_const("t_before_12");
		    expr t_after_12 = c.int_const("t_after_12");
		    s.add(t_before_12 >= (int)segLower + 1 && t_before_12 <= (int)segUpper && t_after_12 >= (int)segLower && t_after_12 <= (int)segUpper);
		    
		    func_decl rho_12 = function("rho_12", c.int_sort(), c.int_sort());
		    func_decl rho_primed_12 = function("rho_primed_12", c.real_sort(), c.real_sort());
		    
		    func_decl rho_21 = function("rho_21", c.int_sort(), c.int_sort());
		    func_decl rho_primed_21 = function("rho_primed_21", c.real_sort(), c.real_sort());
		    
		    expr pwl_12 = c.int_const("pwl_12");
		    s.add(pwl_12 >= (int)segLower + 1 && pwl_12 <= (int)segUpper);
		    
		    expr pwl_21 = c.int_const("pwl_21");
		    s.add(pwl_21 >= (int)segLower + 1 && pwl_21 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_12(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_12(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_21(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_21(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_12, t_after_12, implies(((t_before_12 < t_after_12) && (t_before_12 >= (int)segLower + 1) && (t_before_12 <= (int)segUpper) && (t_after_12 >= (int)segLower) && (t_after_12 <= (int)segUpper)), ((rho_12(t_before_12) < rho_12(t_after_12)) && (rho_21(t_before_12) < rho_21(t_after_12))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_2, implies(((rho_12(pred_1) == pred_2) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_2 >= (int)segLower) && (pred_2 <= (int)segUpper)), (c.real_val(delta) <= (((a_2_x(pred_2) - a_1_x(pred_1)) * (a_2_x(pred_2) - a_1_x(pred_1))) + ((a_2_y(pred_2) - a_1_y(pred_1)) * (a_2_y(pred_2) - a_1_y(pred_1))) + ((a_2_z(pred_2) - a_1_z(pred_1)) * (a_2_z(pred_2) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_12, implies(((pwl_12 >= (int)segLower + 1) && (pwl_12 <= (int)segUpper)), (rho_primed_12(pwl_12) == rho_12(c.int_val(pwl_12)) + ((pwl_12 - c.int_val(pwl_12)) * (rho_12(c.int_val(pwl_12) + 1) - rho_12(c.int_val(pwl_12))))))));
			s.add(forall(pwl_21, implies(((pwl_21 >= (int)segLower + 1) && (pwl_21 <= (int)segUpper)), (rho_primed_21(pwl_21) == rho_21(c.int_val(pwl_21)) + ((pwl_21 - c.int_val(pwl_21)) * (rho_21(c.int_val(pwl_21) + 1) - rho_21(c.int_val(pwl_21))))))));
			
			//inverse re-timing
			s.add(forall(t_12, implies(((t_12 >= (int)segLower) && (t_12 <= (int)segUpper)), (rho_21(rho_12(t_12)) == t_12))));

			// ================ AGENT 1 AND AGENT 2 END ================ //
			
			// =============== AGENT 1 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_13 = c.int_const("t_13");
		    s.add(t_13 >= (int)segLower + 1 && t_13 <= (int)segUpper);
		    
		    expr t_before_13 = c.int_const("t_before_13");
		    expr t_after_13 = c.int_const("t_after_13");
		    s.add(t_before_13 >= (int)segLower + 1 && t_before_13 <= (int)segUpper && t_after_13 >= (int)segLower && t_after_13 <= (int)segUpper);
		    
		    func_decl rho_13 = function("rho_13", c.int_sort(), c.int_sort());
		    func_decl rho_primed_13 = function("rho_primed_13", c.real_sort(), c.real_sort());
		    
		    func_decl rho_31 = function("rho_31", c.int_sort(), c.int_sort());
		    func_decl rho_primed_31 = function("rho_primed_31", c.real_sort(), c.real_sort());
		    
		    expr pwl_13 = c.int_const("pwl_13");
		    s.add(pwl_13 >= (int)segLower + 1 && pwl_13 <= (int)segUpper);
		    
		    expr pwl_31 = c.int_const("pwl_31");
		    s.add(pwl_31 >= (int)segLower + 1 && pwl_31 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_13(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_13(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_31(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_31(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_13, t_after_13, implies(((t_before_13 < t_after_13) && (t_before_13 >= (int)segLower + 1) && (t_before_13 <= (int)segUpper) && (t_after_13 >= (int)segLower) && (t_after_13 <= (int)segUpper)), ((rho_13(t_before_13) < rho_13(t_after_13)) && (rho_31(t_before_13) < rho_31(t_after_13))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_3, implies(((rho_13(pred_1) == pred_3) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_1_x(pred_1)) * (a_3_x(pred_3) - a_1_x(pred_1))) + ((a_3_y(pred_3) - a_1_y(pred_1)) * (a_3_y(pred_3) - a_1_y(pred_1))) + ((a_3_z(pred_3) - a_1_z(pred_1)) * (a_3_z(pred_3) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_13, implies(((pwl_13 >= (int)segLower + 1) && (pwl_13 <= (int)segUpper)), (rho_primed_13(pwl_13) == rho_13(c.int_val(pwl_13)) + ((pwl_13 - c.int_val(pwl_13)) * (rho_13(c.int_val(pwl_13) + 1) - rho_13(c.int_val(pwl_13))))))));
			s.add(forall(pwl_31, implies(((pwl_31 >= (int)segLower + 1) && (pwl_31 <= (int)segUpper)), (rho_primed_31(pwl_31) == rho_31(c.int_val(pwl_31)) + ((pwl_31 - c.int_val(pwl_31)) * (rho_31(c.int_val(pwl_31) + 1) - rho_31(c.int_val(pwl_31))))))));
			
			//inverse re-timing
			s.add(forall(t_13, implies(((t_13 >= (int)segLower) && (t_13 <= (int)segUpper)), (rho_31(rho_13(t_13)) == t_13))));

			// ================ AGENT 1 AND AGENT 3 END ================ //
			
			// =============== AGENT 1 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_14 = c.int_const("t_14");
		    s.add(t_14 >= (int)segLower + 1 && t_14 <= (int)segUpper);
		    
		    expr t_before_14 = c.int_const("t_before_14");
		    expr t_after_14 = c.int_const("t_after_14");
		    s.add(t_before_14 >= (int)segLower + 1 && t_before_14 <= (int)segUpper && t_after_14 >= (int)segLower && t_after_14 <= (int)segUpper);
		    
		    func_decl rho_14 = function("rho_14", c.int_sort(), c.int_sort());
		    func_decl rho_primed_14 = function("rho_primed_14", c.real_sort(), c.real_sort());
		    
		    func_decl rho_41 = function("rho_41", c.int_sort(), c.int_sort());
		    func_decl rho_primed_41 = function("rho_primed_41", c.real_sort(), c.real_sort());
		    
		    expr pwl_14 = c.int_const("pwl_14");
		    s.add(pwl_14 >= (int)segLower + 1 && pwl_14 <= (int)segUpper);
		    
		    expr pwl_41 = c.int_const("pwl_41");
		    s.add(pwl_41 >= (int)segLower + 1 && pwl_41 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_14(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_14(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_41(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_41(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_14, t_after_14, implies(((t_before_14 < t_after_14) && (t_before_14 >= (int)segLower + 1) && (t_before_14 <= (int)segUpper) && (t_after_14 >= (int)segLower) && (t_after_14 <= (int)segUpper)), ((rho_14(t_before_14) < rho_14(t_after_14)) && (rho_41(t_before_14) < rho_41(t_after_14))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_4, implies(((rho_14(pred_1) == pred_4) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_1_x(pred_1)) * (a_4_x(pred_4) - a_1_x(pred_1))) + ((a_4_y(pred_4) - a_1_y(pred_1)) * (a_4_y(pred_4) - a_1_y(pred_1))) + ((a_4_z(pred_4) - a_1_z(pred_1)) * (a_4_z(pred_4) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_14, implies(((pwl_14 >= (int)segLower + 1) && (pwl_14 <= (int)segUpper)), (rho_primed_14(pwl_14) == rho_14(c.int_val(pwl_14)) + ((pwl_14 - c.int_val(pwl_14)) * (rho_14(c.int_val(pwl_14) + 1) - rho_14(c.int_val(pwl_14))))))));
			s.add(forall(pwl_41, implies(((pwl_41 >= (int)segLower + 1) && (pwl_41 <= (int)segUpper)), (rho_primed_41(pwl_41) == rho_41(c.int_val(pwl_41)) + ((pwl_41 - c.int_val(pwl_41)) * (rho_41(c.int_val(pwl_41) + 1) - rho_41(c.int_val(pwl_41))))))));
			
			//inverse re-timing
			s.add(forall(t_14, implies(((t_14 >= (int)segLower) && (t_14 <= (int)segUpper)), (rho_41(rho_14(t_14)) == t_14))));

			// ================ AGENT 1 AND AGENT 4 END ================ //
			
			// =============== AGENT 1 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_15 = c.int_const("t_15");
		    s.add(t_15 >= (int)segLower + 1 && t_15 <= (int)segUpper);
		    
		    expr t_before_15 = c.int_const("t_before_15");
		    expr t_after_15 = c.int_const("t_after_15");
		    s.add(t_before_15 >= (int)segLower + 1 && t_before_15 <= (int)segUpper && t_after_15 >= (int)segLower && t_after_15 <= (int)segUpper);
		    
		    func_decl rho_15 = function("rho_15", c.int_sort(), c.int_sort());
		    func_decl rho_primed_15 = function("rho_primed_15", c.real_sort(), c.real_sort());
		    
		    func_decl rho_51 = function("rho_51", c.int_sort(), c.int_sort());
		    func_decl rho_primed_51 = function("rho_primed_51", c.real_sort(), c.real_sort());
		    
		    expr pwl_15 = c.int_const("pwl_15");
		    s.add(pwl_15 >= (int)segLower + 1 && pwl_15 <= (int)segUpper);
		    
		    expr pwl_51 = c.int_const("pwl_51");
		    s.add(pwl_51 >= (int)segLower + 1 && pwl_51 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_15(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_15(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_51(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_51(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_15, t_after_15, implies(((t_before_15 < t_after_15) && (t_before_15 >= (int)segLower + 1) && (t_before_15 <= (int)segUpper) && (t_after_15 >= (int)segLower) && (t_after_15 <= (int)segUpper)), ((rho_15(t_before_15) < rho_15(t_after_15)) && (rho_51(t_before_15) < rho_51(t_after_15))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_5, implies(((rho_15(pred_1) == pred_5) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_1_x(pred_1)) * (a_5_x(pred_5) - a_1_x(pred_1))) + ((a_5_y(pred_5) - a_1_y(pred_1)) * (a_5_y(pred_5) - a_1_y(pred_1))) + ((a_5_z(pred_5) - a_1_z(pred_1)) * (a_5_z(pred_5) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_15, implies(((pwl_15 >= (int)segLower + 1) && (pwl_15 <= (int)segUpper)), (rho_primed_15(pwl_15) == rho_15(c.int_val(pwl_15)) + ((pwl_15 - c.int_val(pwl_15)) * (rho_15(c.int_val(pwl_15) + 1) - rho_15(c.int_val(pwl_15))))))));
			s.add(forall(pwl_51, implies(((pwl_51 >= (int)segLower + 1) && (pwl_51 <= (int)segUpper)), (rho_primed_51(pwl_51) == rho_51(c.int_val(pwl_51)) + ((pwl_51 - c.int_val(pwl_51)) * (rho_51(c.int_val(pwl_51) + 1) - rho_51(c.int_val(pwl_51))))))));
			
			//inverse re-timing
			s.add(forall(t_15, implies(((t_15 >= (int)segLower) && (t_15 <= (int)segUpper)), (rho_51(rho_15(t_15)) == t_15))));

			// ================ AGENT 1 AND AGENT 5 END ================ //
			
			// =============== AGENT 1 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_16 = c.int_const("t_16");
		    s.add(t_16 >= (int)segLower + 1 && t_16 <= (int)segUpper);
		    
		    expr t_before_16 = c.int_const("t_before_16");
		    expr t_after_16 = c.int_const("t_after_16");
		    s.add(t_before_16 >= (int)segLower + 1 && t_before_16 <= (int)segUpper && t_after_16 >= (int)segLower && t_after_16 <= (int)segUpper);
		    
		    func_decl rho_16 = function("rho_16", c.int_sort(), c.int_sort());
		    func_decl rho_primed_16 = function("rho_primed_16", c.real_sort(), c.real_sort());
		    
		    func_decl rho_61 = function("rho_61", c.int_sort(), c.int_sort());
		    func_decl rho_primed_61 = function("rho_primed_61", c.real_sort(), c.real_sort());
		    
		    expr pwl_16 = c.int_const("pwl_16");
		    s.add(pwl_16 >= (int)segLower + 1 && pwl_16 <= (int)segUpper);
		    
		    expr pwl_61 = c.int_const("pwl_61");
		    s.add(pwl_61 >= (int)segLower + 1 && pwl_61 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_16(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_16(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_61(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_61(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_16, t_after_16, implies(((t_before_16 < t_after_16) && (t_before_16 >= (int)segLower + 1) && (t_before_16 <= (int)segUpper) && (t_after_16 >= (int)segLower) && (t_after_16 <= (int)segUpper)), ((rho_16(t_before_16) < rho_16(t_after_16)) && (rho_61(t_before_16) < rho_61(t_after_16))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_6, implies(((rho_16(pred_1) == pred_6) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_1_x(pred_1)) * (a_6_x(pred_6) - a_1_x(pred_1))) + ((a_6_y(pred_6) - a_1_y(pred_1)) * (a_6_y(pred_6) - a_1_y(pred_1))) + ((a_6_z(pred_6) - a_1_z(pred_1)) * (a_6_z(pred_6) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_16, implies(((pwl_16 >= (int)segLower + 1) && (pwl_16 <= (int)segUpper)), (rho_primed_16(pwl_16) == rho_16(c.int_val(pwl_16)) + ((pwl_16 - c.int_val(pwl_16)) * (rho_16(c.int_val(pwl_16) + 1) - rho_16(c.int_val(pwl_16))))))));
			s.add(forall(pwl_61, implies(((pwl_61 >= (int)segLower + 1) && (pwl_61 <= (int)segUpper)), (rho_primed_61(pwl_61) == rho_61(c.int_val(pwl_61)) + ((pwl_61 - c.int_val(pwl_61)) * (rho_61(c.int_val(pwl_61) + 1) - rho_61(c.int_val(pwl_61))))))));
			
			//inverse re-timing
			s.add(forall(t_16, implies(((t_16 >= (int)segLower) && (t_16 <= (int)segUpper)), (rho_61(rho_16(t_16)) == t_16))));

			// ================ AGENT 1 AND AGENT 6 END ================ //
			
			// =============== AGENT 2 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_23 = c.int_const("t_23");
		    s.add(t_23 >= (int)segLower + 1 && t_23 <= (int)segUpper);
		    
		    expr t_before_23 = c.int_const("t_before_23");
		    expr t_after_23 = c.int_const("t_after_23");
		    s.add(t_before_23 >= (int)segLower + 1 && t_before_23 <= (int)segUpper && t_after_23 >= (int)segLower && t_after_23 <= (int)segUpper);
		    
		    func_decl rho_23 = function("rho_23", c.int_sort(), c.int_sort());
		    func_decl rho_primed_23 = function("rho_primed_23", c.real_sort(), c.real_sort());
		    
		    func_decl rho_32 = function("rho_32", c.int_sort(), c.int_sort());
		    func_decl rho_primed_32 = function("rho_primed_32", c.real_sort(), c.real_sort());
		    
		    expr pwl_23 = c.int_const("pwl_23");
		    s.add(pwl_23 >= (int)segLower + 1 && pwl_23 <= (int)segUpper);
		    
		    expr pwl_32 = c.int_const("pwl_32");
		    s.add(pwl_32 >= (int)segLower + 1 && pwl_32 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_23(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_23(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_32(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_32(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_23, t_after_23, implies(((t_before_23 < t_after_23) && (t_before_23 >= (int)segLower + 1) && (t_before_23 <= (int)segUpper) && (t_after_23 >= (int)segLower) && (t_after_23 <= (int)segUpper)), ((rho_23(t_before_23) < rho_23(t_after_23)) && (rho_32(t_before_23) < rho_32(t_after_23))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_3, implies(((rho_23(pred_2) == pred_3) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_2_x(pred_2)) * (a_3_x(pred_3) - a_2_x(pred_2))) + ((a_3_y(pred_3) - a_2_y(pred_2)) * (a_3_y(pred_3) - a_2_y(pred_2))) + ((a_3_z(pred_3) - a_2_z(pred_2)) * (a_3_z(pred_3) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_23, implies(((pwl_23 >= (int)segLower + 1) && (pwl_23 <= (int)segUpper)), (rho_primed_23(pwl_23) == rho_23(c.int_val(pwl_23)) + ((pwl_23 - c.int_val(pwl_23)) * (rho_23(c.int_val(pwl_23) + 1) - rho_23(c.int_val(pwl_23))))))));
			s.add(forall(pwl_32, implies(((pwl_32 >= (int)segLower + 1) && (pwl_32 <= (int)segUpper)), (rho_primed_32(pwl_32) == rho_32(c.int_val(pwl_32)) + ((pwl_32 - c.int_val(pwl_32)) * (rho_32(c.int_val(pwl_32) + 1) - rho_32(c.int_val(pwl_32))))))));
			
			//inverse re-timing
			s.add(forall(t_23, implies(((t_23 >= (int)segLower) && (t_23 <= (int)segUpper)), (rho_32(rho_23(t_23)) == t_23))));

			// ================ AGENT 2 AND AGENT 3 END ================ //
			
			// =============== AGENT 2 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_24 = c.int_const("t_24");
		    s.add(t_24 >= (int)segLower + 1 && t_24 <= (int)segUpper);
		    
		    expr t_before_24 = c.int_const("t_before_24");
		    expr t_after_24 = c.int_const("t_after_24");
		    s.add(t_before_24 >= (int)segLower + 1 && t_before_24 <= (int)segUpper && t_after_24 >= (int)segLower && t_after_24 <= (int)segUpper);
		    
		    func_decl rho_24 = function("rho_24", c.int_sort(), c.int_sort());
		    func_decl rho_primed_24 = function("rho_primed_24", c.real_sort(), c.real_sort());
		    
		    func_decl rho_42 = function("rho_42", c.int_sort(), c.int_sort());
		    func_decl rho_primed_42 = function("rho_primed_42", c.real_sort(), c.real_sort());
		    
		    expr pwl_24 = c.int_const("pwl_24");
		    s.add(pwl_24 >= (int)segLower + 1 && pwl_24 <= (int)segUpper);
		    
		    expr pwl_42 = c.int_const("pwl_42");
		    s.add(pwl_42 >= (int)segLower + 1 && pwl_42 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_24(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_24(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_42(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_42(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_24, t_after_24, implies(((t_before_24 < t_after_24) && (t_before_24 >= (int)segLower + 1) && (t_before_24 <= (int)segUpper) && (t_after_24 >= (int)segLower) && (t_after_24 <= (int)segUpper)), ((rho_24(t_before_24) < rho_24(t_after_24)) && (rho_42(t_before_24) < rho_42(t_after_24))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_4, implies(((rho_24(pred_2) == pred_4) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_2_x(pred_2)) * (a_4_x(pred_4) - a_2_x(pred_2))) + ((a_4_y(pred_4) - a_2_y(pred_2)) * (a_4_y(pred_4) - a_2_y(pred_2))) + ((a_4_z(pred_4) - a_2_z(pred_2)) * (a_4_z(pred_4) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_24, implies(((pwl_24 >= (int)segLower + 1) && (pwl_24 <= (int)segUpper)), (rho_primed_24(pwl_24) == rho_24(c.int_val(pwl_24)) + ((pwl_24 - c.int_val(pwl_24)) * (rho_24(c.int_val(pwl_24) + 1) - rho_24(c.int_val(pwl_24))))))));
			s.add(forall(pwl_42, implies(((pwl_42 >= (int)segLower + 1) && (pwl_42 <= (int)segUpper)), (rho_primed_42(pwl_42) == rho_42(c.int_val(pwl_42)) + ((pwl_42 - c.int_val(pwl_42)) * (rho_42(c.int_val(pwl_42) + 1) - rho_42(c.int_val(pwl_42))))))));
			
			//inverse re-timing
			s.add(forall(t_24, implies(((t_24 >= (int)segLower) && (t_24 <= (int)segUpper)), (rho_42(rho_24(t_24)) == t_24))));

			// ================ AGENT 2 AND AGENT 4 END ================ //
			
			// =============== AGENT 2 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_25 = c.int_const("t_25");
		    s.add(t_25 >= (int)segLower + 1 && t_25 <= (int)segUpper);
		    
		    expr t_before_25 = c.int_const("t_before_25");
		    expr t_after_25 = c.int_const("t_after_25");
		    s.add(t_before_25 >= (int)segLower + 1 && t_before_25 <= (int)segUpper && t_after_25 >= (int)segLower && t_after_25 <= (int)segUpper);
		    
		    func_decl rho_25 = function("rho_25", c.int_sort(), c.int_sort());
		    func_decl rho_primed_25 = function("rho_primed_25", c.real_sort(), c.real_sort());
		    
		    func_decl rho_52 = function("rho_52", c.int_sort(), c.int_sort());
		    func_decl rho_primed_52 = function("rho_primed_52", c.real_sort(), c.real_sort());
		    
		    expr pwl_25 = c.int_const("pwl_25");
		    s.add(pwl_25 >= (int)segLower + 1 && pwl_25 <= (int)segUpper);
		    
		    expr pwl_52 = c.int_const("pwl_52");
		    s.add(pwl_52 >= (int)segLower + 1 && pwl_52 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_25(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_25(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_52(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_52(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_25, t_after_25, implies(((t_before_25 < t_after_25) && (t_before_25 >= (int)segLower + 1) && (t_before_25 <= (int)segUpper) && (t_after_25 >= (int)segLower) && (t_after_25 <= (int)segUpper)), ((rho_25(t_before_25) < rho_25(t_after_25)) && (rho_52(t_before_25) < rho_52(t_after_25))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_5, implies(((rho_25(pred_2) == pred_5) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_2_x(pred_2)) * (a_5_x(pred_5) - a_2_x(pred_2))) + ((a_5_y(pred_5) - a_2_y(pred_2)) * (a_5_y(pred_5) - a_2_y(pred_2))) + ((a_5_z(pred_5) - a_2_z(pred_2)) * (a_5_z(pred_5) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_25, implies(((pwl_25 >= (int)segLower + 1) && (pwl_25 <= (int)segUpper)), (rho_primed_25(pwl_25) == rho_25(c.int_val(pwl_25)) + ((pwl_25 - c.int_val(pwl_25)) * (rho_25(c.int_val(pwl_25) + 1) - rho_25(c.int_val(pwl_25))))))));
			s.add(forall(pwl_52, implies(((pwl_52 >= (int)segLower + 1) && (pwl_52 <= (int)segUpper)), (rho_primed_52(pwl_52) == rho_52(c.int_val(pwl_52)) + ((pwl_52 - c.int_val(pwl_52)) * (rho_52(c.int_val(pwl_52) + 1) - rho_52(c.int_val(pwl_52))))))));
			
			//inverse re-timing
			s.add(forall(t_25, implies(((t_25 >= (int)segLower) && (t_25 <= (int)segUpper)), (rho_52(rho_25(t_25)) == t_25))));

			// ================ AGENT 2 AND AGENT 5 END ================ //
			
			// =============== AGENT 2 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_26 = c.int_const("t_26");
		    s.add(t_26 >= (int)segLower + 1 && t_26 <= (int)segUpper);
		    
		    expr t_before_26 = c.int_const("t_before_26");
		    expr t_after_26 = c.int_const("t_after_26");
		    s.add(t_before_26 >= (int)segLower + 1 && t_before_26 <= (int)segUpper && t_after_26 >= (int)segLower && t_after_26 <= (int)segUpper);
		    
		    func_decl rho_26 = function("rho_26", c.int_sort(), c.int_sort());
		    func_decl rho_primed_26 = function("rho_primed_26", c.real_sort(), c.real_sort());
		    
		    func_decl rho_62 = function("rho_62", c.int_sort(), c.int_sort());
		    func_decl rho_primed_62 = function("rho_primed_62", c.real_sort(), c.real_sort());
		    
		    expr pwl_26 = c.int_const("pwl_26");
		    s.add(pwl_26 >= (int)segLower + 1 && pwl_26 <= (int)segUpper);
		    
		    expr pwl_62 = c.int_const("pwl_62");
		    s.add(pwl_62 >= (int)segLower + 1 && pwl_62 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_26(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_26(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_62(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_62(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_26, t_after_26, implies(((t_before_26 < t_after_26) && (t_before_26 >= (int)segLower + 1) && (t_before_26 <= (int)segUpper) && (t_after_26 >= (int)segLower) && (t_after_26 <= (int)segUpper)), ((rho_26(t_before_26) < rho_26(t_after_26)) && (rho_62(t_before_26) < rho_62(t_after_26))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_6, implies(((rho_26(pred_2) == pred_6) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_2_x(pred_2)) * (a_6_x(pred_6) - a_2_x(pred_2))) + ((a_6_y(pred_6) - a_2_y(pred_2)) * (a_6_y(pred_6) - a_2_y(pred_2))) + ((a_6_z(pred_6) - a_2_z(pred_2)) * (a_6_z(pred_6) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_26, implies(((pwl_26 >= (int)segLower + 1) && (pwl_26 <= (int)segUpper)), (rho_primed_26(pwl_26) == rho_26(c.int_val(pwl_26)) + ((pwl_26 - c.int_val(pwl_26)) * (rho_26(c.int_val(pwl_26) + 1) - rho_26(c.int_val(pwl_26))))))));
			s.add(forall(pwl_62, implies(((pwl_62 >= (int)segLower + 1) && (pwl_62 <= (int)segUpper)), (rho_primed_62(pwl_62) == rho_62(c.int_val(pwl_62)) + ((pwl_62 - c.int_val(pwl_62)) * (rho_62(c.int_val(pwl_62) + 1) - rho_62(c.int_val(pwl_62))))))));
			
			//inverse re-timing
			s.add(forall(t_26, implies(((t_26 >= (int)segLower) && (t_26 <= (int)segUpper)), (rho_62(rho_26(t_26)) == t_26))));

			// ================ AGENT 2 AND AGENT 6 END ================ //
			
			// =============== AGENT 3 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_34 = c.int_const("t_34");
		    s.add(t_34 >= (int)segLower + 1 && t_34 <= (int)segUpper);
		    
		    expr t_before_34 = c.int_const("t_before_34");
		    expr t_after_34 = c.int_const("t_after_34");
		    s.add(t_before_34 >= (int)segLower + 1 && t_before_34 <= (int)segUpper && t_after_34 >= (int)segLower && t_after_34 <= (int)segUpper);
		    
		    func_decl rho_34 = function("rho_34", c.int_sort(), c.int_sort());
		    func_decl rho_primed_34 = function("rho_primed_34", c.real_sort(), c.real_sort());
		    
		    func_decl rho_43 = function("rho_43", c.int_sort(), c.int_sort());
		    func_decl rho_primed_43 = function("rho_primed_43", c.real_sort(), c.real_sort());
		    
		    expr pwl_34 = c.int_const("pwl_34");
		    s.add(pwl_34 >= (int)segLower + 1 && pwl_34 <= (int)segUpper);
		    
		    expr pwl_43 = c.int_const("pwl_43");
		    s.add(pwl_43 >= (int)segLower + 1 && pwl_43 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_34(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_34(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_43(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_43(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_34, t_after_34, implies(((t_before_34 < t_after_34) && (t_before_34 >= (int)segLower + 1) && (t_before_34 <= (int)segUpper) && (t_after_34 >= (int)segLower) && (t_after_34 <= (int)segUpper)), ((rho_34(t_before_34) < rho_34(t_after_34)) && (rho_43(t_before_34) < rho_43(t_after_34))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_4, implies(((rho_34(pred_3) == pred_4) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_3_x(pred_3)) * (a_4_x(pred_4) - a_3_x(pred_3))) + ((a_4_y(pred_4) - a_3_y(pred_3)) * (a_4_y(pred_4) - a_3_y(pred_3))) + ((a_4_z(pred_4) - a_3_z(pred_3)) * (a_4_z(pred_4) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_34, implies(((pwl_34 >= (int)segLower + 1) && (pwl_34 <= (int)segUpper)), (rho_primed_34(pwl_34) == rho_34(c.int_val(pwl_34)) + ((pwl_34 - c.int_val(pwl_34)) * (rho_34(c.int_val(pwl_34) + 1) - rho_34(c.int_val(pwl_34))))))));
			s.add(forall(pwl_43, implies(((pwl_43 >= (int)segLower + 1) && (pwl_43 <= (int)segUpper)), (rho_primed_43(pwl_43) == rho_43(c.int_val(pwl_43)) + ((pwl_43 - c.int_val(pwl_43)) * (rho_43(c.int_val(pwl_43) + 1) - rho_43(c.int_val(pwl_43))))))));
			
			//inverse re-timing
			s.add(forall(t_34, implies(((t_34 >= (int)segLower) && (t_34 <= (int)segUpper)), (rho_43(rho_34(t_34)) == t_34))));

			// ================ AGENT 3 AND AGENT 4 END ================ //
			
			// =============== AGENT 3 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_35 = c.int_const("t_35");
		    s.add(t_35 >= (int)segLower + 1 && t_35 <= (int)segUpper);
		    
		    expr t_before_35 = c.int_const("t_before_35");
		    expr t_after_35 = c.int_const("t_after_35");
		    s.add(t_before_35 >= (int)segLower + 1 && t_before_35 <= (int)segUpper && t_after_35 >= (int)segLower && t_after_35 <= (int)segUpper);
		    
		    func_decl rho_35 = function("rho_35", c.int_sort(), c.int_sort());
		    func_decl rho_primed_35 = function("rho_primed_35", c.real_sort(), c.real_sort());
		    
		    func_decl rho_53 = function("rho_53", c.int_sort(), c.int_sort());
		    func_decl rho_primed_53 = function("rho_primed_53", c.real_sort(), c.real_sort());
		    
		    expr pwl_35 = c.int_const("pwl_35");
		    s.add(pwl_35 >= (int)segLower + 1 && pwl_35 <= (int)segUpper);
		    
		    expr pwl_53 = c.int_const("pwl_53");
		    s.add(pwl_53 >= (int)segLower + 1 && pwl_53 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_35(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_35(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_53(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_53(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_35, t_after_35, implies(((t_before_35 < t_after_35) && (t_before_35 >= (int)segLower + 1) && (t_before_35 <= (int)segUpper) && (t_after_35 >= (int)segLower) && (t_after_35 <= (int)segUpper)), ((rho_35(t_before_35) < rho_35(t_after_35)) && (rho_53(t_before_35) < rho_53(t_after_35))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_5, implies(((rho_35(pred_3) == pred_5) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_3_x(pred_3)) * (a_5_x(pred_5) - a_3_x(pred_3))) + ((a_5_y(pred_5) - a_3_y(pred_3)) * (a_5_y(pred_5) - a_3_y(pred_3))) + ((a_5_z(pred_5) - a_3_z(pred_3)) * (a_5_z(pred_5) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_35, implies(((pwl_35 >= (int)segLower + 1) && (pwl_35 <= (int)segUpper)), (rho_primed_35(pwl_35) == rho_35(c.int_val(pwl_35)) + ((pwl_35 - c.int_val(pwl_35)) * (rho_35(c.int_val(pwl_35) + 1) - rho_35(c.int_val(pwl_35))))))));
			s.add(forall(pwl_53, implies(((pwl_53 >= (int)segLower + 1) && (pwl_53 <= (int)segUpper)), (rho_primed_53(pwl_53) == rho_53(c.int_val(pwl_53)) + ((pwl_53 - c.int_val(pwl_53)) * (rho_53(c.int_val(pwl_53) + 1) - rho_53(c.int_val(pwl_53))))))));
			
			//inverse re-timing
			s.add(forall(t_35, implies(((t_35 >= (int)segLower) && (t_35 <= (int)segUpper)), (rho_53(rho_35(t_35)) == t_35))));

			// ================ AGENT 3 AND AGENT 5 END ================ //
			
			// =============== AGENT 3 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_36 = c.int_const("t_36");
		    s.add(t_36 >= (int)segLower + 1 && t_36 <= (int)segUpper);
		    
		    expr t_before_36 = c.int_const("t_before_36");
		    expr t_after_36 = c.int_const("t_after_36");
		    s.add(t_before_36 >= (int)segLower + 1 && t_before_36 <= (int)segUpper && t_after_36 >= (int)segLower && t_after_36 <= (int)segUpper);
		    
		    func_decl rho_36 = function("rho_36", c.int_sort(), c.int_sort());
		    func_decl rho_primed_36 = function("rho_primed_36", c.real_sort(), c.real_sort());
		    
		    func_decl rho_63 = function("rho_63", c.int_sort(), c.int_sort());
		    func_decl rho_primed_63 = function("rho_primed_63", c.real_sort(), c.real_sort());
		    
		    expr pwl_36 = c.int_const("pwl_36");
		    s.add(pwl_36 >= (int)segLower + 1 && pwl_36 <= (int)segUpper);
		    
		    expr pwl_63 = c.int_const("pwl_63");
		    s.add(pwl_63 >= (int)segLower + 1 && pwl_63 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_36(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_36(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_63(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_63(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_36, t_after_36, implies(((t_before_36 < t_after_36) && (t_before_36 >= (int)segLower + 1) && (t_before_36 <= (int)segUpper) && (t_after_36 >= (int)segLower) && (t_after_36 <= (int)segUpper)), ((rho_36(t_before_36) < rho_36(t_after_36)) && (rho_63(t_before_36) < rho_63(t_after_36))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_6, implies(((rho_36(pred_3) == pred_6) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_3_x(pred_3)) * (a_6_x(pred_6) - a_3_x(pred_3))) + ((a_6_y(pred_6) - a_3_y(pred_3)) * (a_6_y(pred_6) - a_3_y(pred_3))) + ((a_6_z(pred_6) - a_3_z(pred_3)) * (a_6_z(pred_6) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_36, implies(((pwl_36 >= (int)segLower + 1) && (pwl_36 <= (int)segUpper)), (rho_primed_36(pwl_36) == rho_36(c.int_val(pwl_36)) + ((pwl_36 - c.int_val(pwl_36)) * (rho_36(c.int_val(pwl_36) + 1) - rho_36(c.int_val(pwl_36))))))));
			s.add(forall(pwl_63, implies(((pwl_63 >= (int)segLower + 1) && (pwl_63 <= (int)segUpper)), (rho_primed_63(pwl_63) == rho_63(c.int_val(pwl_63)) + ((pwl_63 - c.int_val(pwl_63)) * (rho_63(c.int_val(pwl_63) + 1) - rho_63(c.int_val(pwl_63))))))));
			
			//inverse re-timing
			s.add(forall(t_36, implies(((t_36 >= (int)segLower) && (t_36 <= (int)segUpper)), (rho_63(rho_36(t_36)) == t_36))));

			// ================ AGENT 3 AND AGENT 6 END ================ //
			
			// =============== AGENT 4 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_45 = c.int_const("t_45");
		    s.add(t_45 >= (int)segLower + 1 && t_45 <= (int)segUpper);
		    
		    expr t_before_45 = c.int_const("t_before_45");
		    expr t_after_45 = c.int_const("t_after_45");
		    s.add(t_before_45 >= (int)segLower + 1 && t_before_45 <= (int)segUpper && t_after_45 >= (int)segLower && t_after_45 <= (int)segUpper);
		    
		    func_decl rho_45 = function("rho_45", c.int_sort(), c.int_sort());
		    func_decl rho_primed_45 = function("rho_primed_45", c.real_sort(), c.real_sort());
		    
		    func_decl rho_54 = function("rho_54", c.int_sort(), c.int_sort());
		    func_decl rho_primed_54 = function("rho_primed_54", c.real_sort(), c.real_sort());
		    
		    expr pwl_45 = c.int_const("pwl_45");
		    s.add(pwl_45 >= (int)segLower + 1 && pwl_45 <= (int)segUpper);
		    
		    expr pwl_54 = c.int_const("pwl_54");
		    s.add(pwl_54 >= (int)segLower + 1 && pwl_54 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_45(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_45(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_54(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_54(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_45, t_after_45, implies(((t_before_45 < t_after_45) && (t_before_45 >= (int)segLower + 1) && (t_before_45 <= (int)segUpper) && (t_after_45 >= (int)segLower) && (t_after_45 <= (int)segUpper)), ((rho_45(t_before_45) < rho_45(t_after_45)) && (rho_54(t_before_45) < rho_54(t_after_45))))));
			
			//mutual separation constraint
			s.add(forall(pred_4, pred_5, implies(((rho_45(pred_4) == pred_5) && (pred_4 >= (int)segLower + 1) && (pred_4 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_4_x(pred_4)) * (a_5_x(pred_5) - a_4_x(pred_4))) + ((a_5_y(pred_5) - a_4_y(pred_4)) * (a_5_y(pred_5) - a_4_y(pred_4))) + ((a_5_z(pred_5) - a_4_z(pred_4)) * (a_5_z(pred_5) - a_4_z(pred_4))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_45, implies(((pwl_45 >= (int)segLower + 1) && (pwl_45 <= (int)segUpper)), (rho_primed_45(pwl_45) == rho_45(c.int_val(pwl_45)) + ((pwl_45 - c.int_val(pwl_45)) * (rho_45(c.int_val(pwl_45) + 1) - rho_45(c.int_val(pwl_45))))))));
			s.add(forall(pwl_54, implies(((pwl_54 >= (int)segLower + 1) && (pwl_54 <= (int)segUpper)), (rho_primed_54(pwl_54) == rho_54(c.int_val(pwl_54)) + ((pwl_54 - c.int_val(pwl_54)) * (rho_54(c.int_val(pwl_54) + 1) - rho_54(c.int_val(pwl_54))))))));
			
			//inverse re-timing
			s.add(forall(t_45, implies(((t_45 >= (int)segLower) && (t_45 <= (int)segUpper)), (rho_54(rho_45(t_45)) == t_45))));

			// ================ AGENT 4 AND AGENT 5 END ================ //
			
			// =============== AGENT 4 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_46 = c.int_const("t_46");
		    s.add(t_46 >= (int)segLower + 1 && t_46 <= (int)segUpper);
		    
		    expr t_before_46 = c.int_const("t_before_46");
		    expr t_after_46 = c.int_const("t_after_46");
		    s.add(t_before_46 >= (int)segLower + 1 && t_before_46 <= (int)segUpper && t_after_46 >= (int)segLower && t_after_46 <= (int)segUpper);
		    
		    func_decl rho_46 = function("rho_46", c.int_sort(), c.int_sort());
		    func_decl rho_primed_46 = function("rho_primed_46", c.real_sort(), c.real_sort());
		    
		    func_decl rho_64 = function("rho_64", c.int_sort(), c.int_sort());
		    func_decl rho_primed_64 = function("rho_primed_64", c.real_sort(), c.real_sort());
		    
		    expr pwl_46 = c.int_const("pwl_46");
		    s.add(pwl_46 >= (int)segLower + 1 && pwl_46 <= (int)segUpper);
		    
		    expr pwl_64 = c.int_const("pwl_64");
		    s.add(pwl_64 >= (int)segLower + 1 && pwl_64 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_46(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_46(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_64(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_64(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_46, t_after_46, implies(((t_before_46 < t_after_46) && (t_before_46 >= (int)segLower + 1) && (t_before_46 <= (int)segUpper) && (t_after_46 >= (int)segLower) && (t_after_46 <= (int)segUpper)), ((rho_46(t_before_46) < rho_46(t_after_46)) && (rho_64(t_before_46) < rho_64(t_after_46))))));
			
			//mutual separation constraint
			s.add(forall(pred_4, pred_6, implies(((rho_46(pred_4) == pred_6) && (pred_4 >= (int)segLower + 1) && (pred_4 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_4_x(pred_4)) * (a_6_x(pred_6) - a_4_x(pred_4))) + ((a_6_y(pred_6) - a_4_y(pred_4)) * (a_6_y(pred_6) - a_4_y(pred_4))) + ((a_6_z(pred_6) - a_4_z(pred_4)) * (a_6_z(pred_6) - a_4_z(pred_4))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_46, implies(((pwl_46 >= (int)segLower + 1) && (pwl_46 <= (int)segUpper)), (rho_primed_46(pwl_46) == rho_46(c.int_val(pwl_46)) + ((pwl_46 - c.int_val(pwl_46)) * (rho_46(c.int_val(pwl_46) + 1) - rho_46(c.int_val(pwl_46))))))));
			s.add(forall(pwl_64, implies(((pwl_64 >= (int)segLower + 1) && (pwl_64 <= (int)segUpper)), (rho_primed_64(pwl_64) == rho_64(c.int_val(pwl_64)) + ((pwl_64 - c.int_val(pwl_64)) * (rho_64(c.int_val(pwl_64) + 1) - rho_64(c.int_val(pwl_64))))))));
			
			//inverse re-timing
			s.add(forall(t_46, implies(((t_46 >= (int)segLower) && (t_46 <= (int)segUpper)), (rho_64(rho_46(t_46)) == t_46))));

			// ================ AGENT 4 AND AGENT 6 END ================ //
			
			// =============== AGENT 5 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_56 = c.int_const("t_56");
		    s.add(t_56 >= (int)segLower + 1 && t_56 <= (int)segUpper);
		    
		    expr t_before_56 = c.int_const("t_before_56");
		    expr t_after_56 = c.int_const("t_after_56");
		    s.add(t_before_56 >= (int)segLower + 1 && t_before_56 <= (int)segUpper && t_after_56 >= (int)segLower && t_after_56 <= (int)segUpper);
		    
		    func_decl rho_56 = function("rho_56", c.int_sort(), c.int_sort());
		    func_decl rho_primed_56 = function("rho_primed_56", c.real_sort(), c.real_sort());
		    
		    func_decl rho_65 = function("rho_65", c.int_sort(), c.int_sort());
		    func_decl rho_primed_65 = function("rho_primed_65", c.real_sort(), c.real_sort());
		    
		    expr pwl_56 = c.int_const("pwl_56");
		    s.add(pwl_56 >= (int)segLower + 1 && pwl_56 <= (int)segUpper);
		    
		    expr pwl_65 = c.int_const("pwl_65");
		    s.add(pwl_65 >= (int)segLower + 1 && pwl_65 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_56(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_56(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_65(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_65(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_56, t_after_56, implies(((t_before_56 < t_after_56) && (t_before_56 >= (int)segLower + 1) && (t_before_56 <= (int)segUpper) && (t_after_56 >= (int)segLower) && (t_after_56 <= (int)segUpper)), ((rho_56(t_before_56) < rho_56(t_after_56)) && (rho_65(t_before_56) < rho_65(t_after_56))))));
			
			//mutual separation constraint
			s.add(forall(pred_5, pred_6, implies(((rho_56(pred_5) == pred_6) && (pred_5 >= (int)segLower + 1) && (pred_5 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_5_x(pred_5)) * (a_6_x(pred_6) - a_5_x(pred_5))) + ((a_6_y(pred_6) - a_5_y(pred_5)) * (a_6_y(pred_6) - a_5_y(pred_5))) + ((a_6_z(pred_6) - a_5_z(pred_5)) * (a_6_z(pred_6) - a_5_z(pred_5))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_56, implies(((pwl_56 >= (int)segLower + 1) && (pwl_56 <= (int)segUpper)), (rho_primed_56(pwl_56) == rho_56(c.int_val(pwl_56)) + ((pwl_56 - c.int_val(pwl_56)) * (rho_56(c.int_val(pwl_56) + 1) - rho_56(c.int_val(pwl_56))))))));
			s.add(forall(pwl_65, implies(((pwl_65 >= (int)segLower + 1) && (pwl_65 <= (int)segUpper)), (rho_primed_65(pwl_65) == rho_65(c.int_val(pwl_65)) + ((pwl_65 - c.int_val(pwl_65)) * (rho_65(c.int_val(pwl_65) + 1) - rho_65(c.int_val(pwl_65))))))));
			
			//inverse re-timing
			s.add(forall(t_56, implies(((t_56 >= (int)segLower) && (t_56 <= (int)segUpper)), (rho_65(rho_56(t_56)) == t_56))));

			// ================ AGENT 5 AND AGENT 6 END ================ //
			
			if(s.check() == sat)
		    {
		    	std::string verdict = std::to_string(i) + " : Sat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    else
		    {
		    	std::string verdict = std::to_string(i) + " : Unsat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    
		    //reset solver
		    //s.reset();
		    
		    //build and show model
		    //model m = s.get_model();
    		//std::cout << m << "\n";
	    }
	}
	//return verdicts;
}

void runSolver_8(double eps, int segCount, double sigDur, int msgLim)
{
	//enable parallel mode
	//set_param("parallel.enable", true);
	
	//get data
	std::vector<std::vector<std::string>> agentData_0 = getData("agent_0.txt");
	std::vector<std::vector<std::string>> agentData_1 = getData("agent_1.txt");
	std::vector<std::vector<std::string>> agentData_2 = getData("agent_2.txt");
	std::vector<std::vector<std::string>> agentData_3 = getData("agent_3.txt");
	std::vector<std::vector<std::string>> agentData_4 = getData("agent_4.txt");
	std::vector<std::vector<std::string>> agentData_5 = getData("agent_5.txt");
	std::vector<std::vector<std::string>> agentData_6 = getData("agent_6.txt");
	std::vector<std::vector<std::string>> agentData_7 = getData("agent_7.txt");
	
	//safety checks
	if(!(std::stod(agentData_0[0][0]) == 0 && std::stod(agentData_1[0][0]) == 0))
	{
		return;
	}
	
	if(std::stod(agentData_0[1][0]) != std::stod(agentData_1[1][0]))
	{
		return;
	}
	
	//second time-stamp on agent that is to be re-timed
	double t1 = std::stod(agentData_0[1][0]);
	
	//delta
	int delta = 0;
	
	//segment duration
	double segDur = sigDur / segCount;
	
	//check if the segment duration is smaller than the sampling period
	if(segDur < t1)
	{
		segCount = sigDur / t1;
	}
	
	//multiplier for normalization
	double mult = 1 / t1;
	
	//normalization of paramters
	eps *= mult;
	sigDur *= mult;
	segDur *= mult;
	
	//verdict vector
	std::vector<std::string> verdicts;
	
	#pragma omp parallel
	{
		#pragma omp for
		for(int i = 0; i < segCount; i++) 
	    {			
			//segment bounds
			double segLower = (i * segDur) - eps;
			double segUpper = (i + 1) * segDur;
			
		    context c;

		    //solver
		    solver s(c);
		    
		    //co-ord functions
		    func_decl a_0_x = function("a_0_x", c.int_sort(), c.real_sort());
		    func_decl a_0_y = function("a_0_y", c.int_sort(), c.real_sort());
		    func_decl a_0_z = function("a_0_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_1_x = function("a_1_x", c.int_sort(), c.real_sort());
		    func_decl a_1_y = function("a_1_y", c.int_sort(), c.real_sort());
		    func_decl a_1_z = function("a_1_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_2_x = function("a_2_x", c.int_sort(), c.real_sort());
		    func_decl a_2_y = function("a_2_y", c.int_sort(), c.real_sort());
		    func_decl a_2_z = function("a_2_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_3_x = function("a_3_x", c.int_sort(), c.real_sort());
		    func_decl a_3_y = function("a_3_y", c.int_sort(), c.real_sort());
		    func_decl a_3_z = function("a_3_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_4_x = function("a_4_x", c.int_sort(), c.real_sort());
		    func_decl a_4_y = function("a_4_y", c.int_sort(), c.real_sort());
		    func_decl a_4_z = function("a_4_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_5_x = function("a_5_x", c.int_sort(), c.real_sort());
		    func_decl a_5_y = function("a_5_y", c.int_sort(), c.real_sort());
		    func_decl a_5_z = function("a_5_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_6_x = function("a_6_x", c.int_sort(), c.real_sort());
		    func_decl a_6_y = function("a_6_y", c.int_sort(), c.real_sort());
		    func_decl a_6_z = function("a_6_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_7_x = function("a_7_x", c.int_sort(), c.real_sort());
		    func_decl a_7_y = function("a_7_y", c.int_sort(), c.real_sort());
		    func_decl a_7_z = function("a_7_z", c.int_sort(), c.real_sort());
		    
		    //populate co-ord functions
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_0.size())
		        {
		        	s.add(a_0_x(j) == c.real_val(agentData_0[j][1].c_str()));
		        	s.add(a_0_y(j) == c.real_val(agentData_0[j][2].c_str()));
		        	s.add(a_0_z(j) == c.real_val(agentData_0[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_1.size())
		        {
		        	s.add(a_1_x(j) == c.real_val(agentData_1[j][1].c_str()));
		        	s.add(a_1_y(j) == c.real_val(agentData_1[j][2].c_str()));
		        	s.add(a_1_z(j) == c.real_val(agentData_1[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_2.size())
		        {
		        	s.add(a_2_x(j) == c.real_val(agentData_2[j][1].c_str()));
		        	s.add(a_2_y(j) == c.real_val(agentData_2[j][2].c_str()));
		        	s.add(a_2_z(j) == c.real_val(agentData_2[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_3.size())
		        {
		        	s.add(a_3_x(j) == c.real_val(agentData_3[j][1].c_str()));
		        	s.add(a_3_y(j) == c.real_val(agentData_3[j][2].c_str()));
		        	s.add(a_3_z(j) == c.real_val(agentData_3[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_4.size())
		        {
		        	s.add(a_4_x(j) == c.real_val(agentData_4[j][1].c_str()));
		        	s.add(a_4_y(j) == c.real_val(agentData_4[j][2].c_str()));
		        	s.add(a_4_z(j) == c.real_val(agentData_4[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_5.size())
		        {
		        	s.add(a_5_x(j) == c.real_val(agentData_5[j][1].c_str()));
		        	s.add(a_5_y(j) == c.real_val(agentData_5[j][2].c_str()));
		        	s.add(a_5_z(j) == c.real_val(agentData_5[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_6.size())
		        {
		        	s.add(a_6_x(j) == c.real_val(agentData_6[j][1].c_str()));
		        	s.add(a_6_y(j) == c.real_val(agentData_6[j][2].c_str()));
		        	s.add(a_6_z(j) == c.real_val(agentData_6[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_7.size())
		        {
		        	s.add(a_7_x(j) == c.real_val(agentData_7[j][1].c_str()));
		        	s.add(a_7_y(j) == c.real_val(agentData_7[j][2].c_str()));
		        	s.add(a_7_z(j) == c.real_val(agentData_7[j][3].c_str()));
				}
		    }
		    
		    //general smt variables		  
			expr pred_0 = c.int_const("pred_0");
			s.add(pred_0 >= (int)segLower + 1 && pred_0 <= (int)segUpper);
			
		    expr pred_1 = c.int_const("pred_1");
		    s.add(pred_1 >= (int)segLower + 1 && pred_1 <= (int)segUpper);
		    
		    expr pred_2 = c.int_const("pred_2");
		    s.add(pred_2 >= (int)segLower + 1 && pred_2 <= (int)segUpper);
		    
		    expr pred_3 = c.int_const("pred_3");
		    s.add(pred_3 >= (int)segLower + 1 && pred_3 <= (int)segUpper);
		    
		    expr pred_4 = c.int_const("pred_4");
		    s.add(pred_4 >= (int)segLower + 1 && pred_4 <= (int)segUpper);
		    
		    expr pred_5 = c.int_const("pred_5");
		    s.add(pred_5 >= (int)segLower + 1 && pred_5 <= (int)segUpper);
		    
		    expr pred_6 = c.int_const("pred_6");
		    s.add(pred_6 >= (int)segLower + 1 && pred_6 <= (int)segUpper);
		    
		    expr pred_7 = c.int_const("pred_7");
		    s.add(pred_7 >= (int)segLower + 1 && pred_7 <= (int)segUpper);
		    
		    // =============== AGENT 0 AND AGENT 1 START =============== //
			
			//agent pair smt variables
			expr t_01 = c.int_const("t_01");
		    s.add(t_01 >= (int)segLower + 1 && t_01 <= (int)segUpper);
		    
		    expr t_before_01 = c.int_const("t_before_01");
		    expr t_after_01 = c.int_const("t_after_01");
		    s.add(t_before_01 >= (int)segLower + 1 && t_before_01 <= (int)segUpper && t_after_01 >= (int)segLower && t_after_01 <= (int)segUpper);
		    
		    func_decl rho_01 = function("rho_01", c.int_sort(), c.int_sort());
		    func_decl rho_primed_01 = function("rho_primed_01", c.real_sort(), c.real_sort());
		    
		    func_decl rho_10 = function("rho_10", c.int_sort(), c.int_sort());
		    func_decl rho_primed_10 = function("rho_primed_10", c.real_sort(), c.real_sort());
		    
		    expr pwl_01 = c.int_const("pwl_01");
		    s.add(pwl_01 >= (int)segLower + 1 && pwl_01 <= (int)segUpper);
		    
		    expr pwl_10 = c.int_const("pwl_10");
		    s.add(pwl_10 >= (int)segLower + 1 && pwl_10 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_01, t_after_01, implies(((t_before_01 < t_after_01) && (t_before_01 >= (int)segLower + 1) && (t_before_01 <= (int)segUpper) && (t_after_01 >= (int)segLower) && (t_after_01 <= (int)segUpper)), ((rho_01(t_before_01) < rho_01(t_after_01)) && (rho_10(t_before_01) < rho_10(t_after_01))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_1, implies(((rho_01(pred_0) == pred_1) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_1 >= (int)segLower) && (pred_1 <= (int)segUpper)), (c.real_val(delta) <= (((a_1_x(pred_1) - a_0_x(pred_0)) * (a_1_x(pred_1) - a_0_x(pred_0))) + ((a_1_y(pred_1) - a_0_y(pred_0)) * (a_1_y(pred_1) - a_0_y(pred_0))) + ((a_1_z(pred_1) - a_0_z(pred_0)) * (a_1_z(pred_1) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_01, implies(((pwl_01 >= (int)segLower + 1) && (pwl_01 <= (int)segUpper)), (rho_primed_01(pwl_01) == rho_01(c.int_val(pwl_01)) + ((pwl_01 - c.int_val(pwl_01)) * (rho_01(c.int_val(pwl_01) + 1) - rho_01(c.int_val(pwl_01))))))));
			s.add(forall(pwl_10, implies(((pwl_10 >= (int)segLower + 1) && (pwl_10 <= (int)segUpper)), (rho_primed_10(pwl_10) == rho_10(c.int_val(pwl_10)) + ((pwl_10 - c.int_val(pwl_10)) * (rho_10(c.int_val(pwl_10) + 1) - rho_10(c.int_val(pwl_10))))))));
			
			//inverse re-timing
			s.add(forall(t_01, implies(((t_01 >= (int)segLower) && (t_01 <= (int)segUpper)), (rho_10(rho_01(t_01)) == t_01))));

			// ================ AGENT 0 AND AGENT 1 END ================ //
			
			// =============== AGENT 0 AND AGENT 2 START =============== //
			
			//agent pair smt variables
			expr t_02 = c.int_const("t_02");
		    s.add(t_02 >= (int)segLower + 1 && t_02 <= (int)segUpper);
		    
		    expr t_before_02 = c.int_const("t_before_02");
		    expr t_after_02 = c.int_const("t_after_02");
		    s.add(t_before_02 >= (int)segLower + 1 && t_before_02 <= (int)segUpper && t_after_02 >= (int)segLower && t_after_02 <= (int)segUpper);
		    
		    func_decl rho_02 = function("rho_02", c.int_sort(), c.int_sort());
		    func_decl rho_primed_02 = function("rho_primed_02", c.real_sort(), c.real_sort());
		    
		    func_decl rho_20 = function("rho_20", c.int_sort(), c.int_sort());
		    func_decl rho_primed_20 = function("rho_primed_20", c.real_sort(), c.real_sort());
		    
		    expr pwl_02 = c.int_const("pwl_02");
		    s.add(pwl_02 >= (int)segLower + 1 && pwl_02 <= (int)segUpper);
		    
		    expr pwl_20 = c.int_const("pwl_20");
		    s.add(pwl_20 >= (int)segLower + 1 && pwl_20 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_02(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_02(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_20(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_20(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_02, t_after_02, implies(((t_before_02 < t_after_02) && (t_before_02 >= (int)segLower + 1) && (t_before_02 <= (int)segUpper) && (t_after_02 >= (int)segLower) && (t_after_02 <= (int)segUpper)), ((rho_02(t_before_02) < rho_02(t_after_02)) && (rho_20(t_before_02) < rho_20(t_after_02))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_2, implies(((rho_02(pred_0) == pred_2) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_2 >= (int)segLower) && (pred_2 <= (int)segUpper)), (c.real_val(delta) <= (((a_2_x(pred_2) - a_0_x(pred_0)) * (a_2_x(pred_2) - a_0_x(pred_0))) + ((a_2_y(pred_2) - a_0_y(pred_0)) * (a_2_y(pred_2) - a_0_y(pred_0))) + ((a_2_z(pred_2) - a_0_z(pred_0)) * (a_2_z(pred_2) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_02, implies(((pwl_02 >= (int)segLower + 1) && (pwl_02 <= (int)segUpper)), (rho_primed_02(pwl_02) == rho_02(c.int_val(pwl_02)) + ((pwl_02 - c.int_val(pwl_02)) * (rho_02(c.int_val(pwl_02) + 1) - rho_02(c.int_val(pwl_02))))))));
			s.add(forall(pwl_20, implies(((pwl_20 >= (int)segLower + 1) && (pwl_20 <= (int)segUpper)), (rho_primed_20(pwl_20) == rho_20(c.int_val(pwl_20)) + ((pwl_20 - c.int_val(pwl_20)) * (rho_20(c.int_val(pwl_20) + 1) - rho_20(c.int_val(pwl_20))))))));
			
			//inverse re-timing
			s.add(forall(t_02, implies(((t_02 >= (int)segLower) && (t_02 <= (int)segUpper)), (rho_20(rho_02(t_02)) == t_02))));

			// ================ AGENT 0 AND AGENT 2 END ================ //
			
			// =============== AGENT 0 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_03 = c.int_const("t_03");
		    s.add(t_03 >= (int)segLower + 1 && t_03 <= (int)segUpper);
		    
		    expr t_before_03 = c.int_const("t_before_03");
		    expr t_after_03 = c.int_const("t_after_03");
		    s.add(t_before_03 >= (int)segLower + 1 && t_before_03 <= (int)segUpper && t_after_03 >= (int)segLower && t_after_03 <= (int)segUpper);
		    
		    func_decl rho_03 = function("rho_03", c.int_sort(), c.int_sort());
		    func_decl rho_primed_03 = function("rho_primed_03", c.real_sort(), c.real_sort());
		    
		    func_decl rho_30 = function("rho_30", c.int_sort(), c.int_sort());
		    func_decl rho_primed_30 = function("rho_primed_30", c.real_sort(), c.real_sort());
		    
		    expr pwl_03 = c.int_const("pwl_03");
		    s.add(pwl_03 >= (int)segLower + 1 && pwl_03 <= (int)segUpper);
		    
		    expr pwl_30 = c.int_const("pwl_30");
		    s.add(pwl_30 >= (int)segLower + 1 && pwl_30 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_03(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_03(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_30(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_30(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_03, t_after_03, implies(((t_before_03 < t_after_03) && (t_before_03 >= (int)segLower + 1) && (t_before_03 <= (int)segUpper) && (t_after_03 >= (int)segLower) && (t_after_03 <= (int)segUpper)), ((rho_03(t_before_03) < rho_03(t_after_03)) && (rho_30(t_before_03) < rho_30(t_after_03))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_3, implies(((rho_03(pred_0) == pred_3) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_0_x(pred_0)) * (a_3_x(pred_3) - a_0_x(pred_0))) + ((a_3_y(pred_3) - a_0_y(pred_0)) * (a_3_y(pred_3) - a_0_y(pred_0))) + ((a_3_z(pred_3) - a_0_z(pred_0)) * (a_3_z(pred_3) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_03, implies(((pwl_03 >= (int)segLower + 1) && (pwl_03 <= (int)segUpper)), (rho_primed_03(pwl_03) == rho_03(c.int_val(pwl_03)) + ((pwl_03 - c.int_val(pwl_03)) * (rho_03(c.int_val(pwl_03) + 1) - rho_03(c.int_val(pwl_03))))))));
			s.add(forall(pwl_30, implies(((pwl_30 >= (int)segLower + 1) && (pwl_30 <= (int)segUpper)), (rho_primed_30(pwl_30) == rho_30(c.int_val(pwl_30)) + ((pwl_30 - c.int_val(pwl_30)) * (rho_30(c.int_val(pwl_30) + 1) - rho_30(c.int_val(pwl_30))))))));
			
			//inverse re-timing
			s.add(forall(t_03, implies(((t_03 >= (int)segLower) && (t_03 <= (int)segUpper)), (rho_30(rho_03(t_03)) == t_03))));

			// ================ AGENT 0 AND AGENT 3 END ================ //
			
			// =============== AGENT 0 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_04 = c.int_const("t_04");
		    s.add(t_04 >= (int)segLower + 1 && t_04 <= (int)segUpper);
		    
		    expr t_before_04 = c.int_const("t_before_04");
		    expr t_after_04 = c.int_const("t_after_04");
		    s.add(t_before_04 >= (int)segLower + 1 && t_before_04 <= (int)segUpper && t_after_04 >= (int)segLower && t_after_04 <= (int)segUpper);
		    
		    func_decl rho_04 = function("rho_04", c.int_sort(), c.int_sort());
		    func_decl rho_primed_04 = function("rho_primed_04", c.real_sort(), c.real_sort());
		    
		    func_decl rho_40 = function("rho_40", c.int_sort(), c.int_sort());
		    func_decl rho_primed_40 = function("rho_primed_40", c.real_sort(), c.real_sort());
		    
		    expr pwl_04 = c.int_const("pwl_04");
		    s.add(pwl_04 >= (int)segLower + 1 && pwl_04 <= (int)segUpper);
		    
		    expr pwl_40 = c.int_const("pwl_40");
		    s.add(pwl_40 >= (int)segLower + 1 && pwl_40 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_04(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_04(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_40(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_40(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_04, t_after_04, implies(((t_before_04 < t_after_04) && (t_before_04 >= (int)segLower + 1) && (t_before_04 <= (int)segUpper) && (t_after_04 >= (int)segLower) && (t_after_04 <= (int)segUpper)), ((rho_04(t_before_04) < rho_04(t_after_04)) && (rho_40(t_before_04) < rho_40(t_after_04))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_4, implies(((rho_04(pred_0) == pred_4) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_0_x(pred_0)) * (a_4_x(pred_4) - a_0_x(pred_0))) + ((a_4_y(pred_4) - a_0_y(pred_0)) * (a_4_y(pred_4) - a_0_y(pred_0))) + ((a_4_z(pred_4) - a_0_z(pred_0)) * (a_4_z(pred_4) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_04, implies(((pwl_04 >= (int)segLower + 1) && (pwl_04 <= (int)segUpper)), (rho_primed_04(pwl_04) == rho_04(c.int_val(pwl_04)) + ((pwl_04 - c.int_val(pwl_04)) * (rho_04(c.int_val(pwl_04) + 1) - rho_04(c.int_val(pwl_04))))))));
			s.add(forall(pwl_40, implies(((pwl_40 >= (int)segLower + 1) && (pwl_40 <= (int)segUpper)), (rho_primed_40(pwl_40) == rho_40(c.int_val(pwl_40)) + ((pwl_40 - c.int_val(pwl_40)) * (rho_40(c.int_val(pwl_40) + 1) - rho_40(c.int_val(pwl_40))))))));
			
			//inverse re-timing
			s.add(forall(t_04, implies(((t_04 >= (int)segLower) && (t_04 <= (int)segUpper)), (rho_40(rho_04(t_04)) == t_04))));

			// ================ AGENT 0 AND AGENT 4 END ================ //
			
			// =============== AGENT 0 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_05 = c.int_const("t_05");
		    s.add(t_05 >= (int)segLower + 1 && t_05 <= (int)segUpper);
		    
		    expr t_before_05 = c.int_const("t_before_05");
		    expr t_after_05 = c.int_const("t_after_05");
		    s.add(t_before_05 >= (int)segLower + 1 && t_before_05 <= (int)segUpper && t_after_05 >= (int)segLower && t_after_05 <= (int)segUpper);
		    
		    func_decl rho_05 = function("rho_05", c.int_sort(), c.int_sort());
		    func_decl rho_primed_05 = function("rho_primed_05", c.real_sort(), c.real_sort());
		    
		    func_decl rho_50 = function("rho_50", c.int_sort(), c.int_sort());
		    func_decl rho_primed_50 = function("rho_primed_50", c.real_sort(), c.real_sort());
		    
		    expr pwl_05 = c.int_const("pwl_05");
		    s.add(pwl_05 >= (int)segLower + 1 && pwl_05 <= (int)segUpper);
		    
		    expr pwl_50 = c.int_const("pwl_50");
		    s.add(pwl_50 >= (int)segLower + 1 && pwl_50 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_05(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_05(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_50(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_50(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_05, t_after_05, implies(((t_before_05 < t_after_05) && (t_before_05 >= (int)segLower + 1) && (t_before_05 <= (int)segUpper) && (t_after_05 >= (int)segLower) && (t_after_05 <= (int)segUpper)), ((rho_05(t_before_05) < rho_05(t_after_05)) && (rho_50(t_before_05) < rho_50(t_after_05))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_5, implies(((rho_05(pred_0) == pred_5) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_0_x(pred_0)) * (a_5_x(pred_5) - a_0_x(pred_0))) + ((a_5_y(pred_5) - a_0_y(pred_0)) * (a_5_y(pred_5) - a_0_y(pred_0))) + ((a_5_z(pred_5) - a_0_z(pred_0)) * (a_5_z(pred_5) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_05, implies(((pwl_05 >= (int)segLower + 1) && (pwl_05 <= (int)segUpper)), (rho_primed_05(pwl_05) == rho_05(c.int_val(pwl_05)) + ((pwl_05 - c.int_val(pwl_05)) * (rho_05(c.int_val(pwl_05) + 1) - rho_05(c.int_val(pwl_05))))))));
			s.add(forall(pwl_50, implies(((pwl_50 >= (int)segLower + 1) && (pwl_50 <= (int)segUpper)), (rho_primed_50(pwl_50) == rho_50(c.int_val(pwl_50)) + ((pwl_50 - c.int_val(pwl_50)) * (rho_50(c.int_val(pwl_50) + 1) - rho_50(c.int_val(pwl_50))))))));
			
			//inverse re-timing
			s.add(forall(t_05, implies(((t_05 >= (int)segLower) && (t_05 <= (int)segUpper)), (rho_50(rho_05(t_05)) == t_05))));

			// ================ AGENT 0 AND AGENT 5 END ================ //
			
			// =============== AGENT 0 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_06 = c.int_const("t_06");
		    s.add(t_06 >= (int)segLower + 1 && t_06 <= (int)segUpper);
		    
		    expr t_before_06 = c.int_const("t_before_06");
		    expr t_after_06 = c.int_const("t_after_06");
		    s.add(t_before_06 >= (int)segLower + 1 && t_before_06 <= (int)segUpper && t_after_06 >= (int)segLower && t_after_06 <= (int)segUpper);
		    
		    func_decl rho_06 = function("rho_06", c.int_sort(), c.int_sort());
		    func_decl rho_primed_06 = function("rho_primed_06", c.real_sort(), c.real_sort());
		    
		    func_decl rho_60 = function("rho_60", c.int_sort(), c.int_sort());
		    func_decl rho_primed_60 = function("rho_primed_60", c.real_sort(), c.real_sort());
		    
		    expr pwl_06 = c.int_const("pwl_06");
		    s.add(pwl_06 >= (int)segLower + 1 && pwl_06 <= (int)segUpper);
		    
		    expr pwl_60 = c.int_const("pwl_60");
		    s.add(pwl_60 >= (int)segLower + 1 && pwl_60 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_06(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_06(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_60(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_60(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_06, t_after_06, implies(((t_before_06 < t_after_06) && (t_before_06 >= (int)segLower + 1) && (t_before_06 <= (int)segUpper) && (t_after_06 >= (int)segLower) && (t_after_06 <= (int)segUpper)), ((rho_06(t_before_06) < rho_06(t_after_06)) && (rho_60(t_before_06) < rho_60(t_after_06))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_6, implies(((rho_06(pred_0) == pred_6) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_0_x(pred_0)) * (a_6_x(pred_6) - a_0_x(pred_0))) + ((a_6_y(pred_6) - a_0_y(pred_0)) * (a_6_y(pred_6) - a_0_y(pred_0))) + ((a_6_z(pred_6) - a_0_z(pred_0)) * (a_6_z(pred_6) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_06, implies(((pwl_06 >= (int)segLower + 1) && (pwl_06 <= (int)segUpper)), (rho_primed_06(pwl_06) == rho_06(c.int_val(pwl_06)) + ((pwl_06 - c.int_val(pwl_06)) * (rho_06(c.int_val(pwl_06) + 1) - rho_06(c.int_val(pwl_06))))))));
			s.add(forall(pwl_60, implies(((pwl_60 >= (int)segLower + 1) && (pwl_60 <= (int)segUpper)), (rho_primed_60(pwl_60) == rho_60(c.int_val(pwl_60)) + ((pwl_60 - c.int_val(pwl_60)) * (rho_60(c.int_val(pwl_60) + 1) - rho_60(c.int_val(pwl_60))))))));
			
			//inverse re-timing
			s.add(forall(t_06, implies(((t_06 >= (int)segLower) && (t_06 <= (int)segUpper)), (rho_60(rho_06(t_06)) == t_06))));

			// ================ AGENT 0 AND AGENT 6 END ================ //
			
			// =============== AGENT 0 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_07 = c.int_const("t_07");
		    s.add(t_07 >= (int)segLower + 1 && t_07 <= (int)segUpper);
		    
		    expr t_before_07 = c.int_const("t_before_07");
		    expr t_after_07 = c.int_const("t_after_07");
		    s.add(t_before_07 >= (int)segLower + 1 && t_before_07 <= (int)segUpper && t_after_07 >= (int)segLower && t_after_07 <= (int)segUpper);
		    
		    func_decl rho_07 = function("rho_07", c.int_sort(), c.int_sort());
		    func_decl rho_primed_07 = function("rho_primed_07", c.real_sort(), c.real_sort());
		    
		    func_decl rho_70 = function("rho_70", c.int_sort(), c.int_sort());
		    func_decl rho_primed_70 = function("rho_primed_70", c.real_sort(), c.real_sort());
		    
		    expr pwl_07 = c.int_const("pwl_07");
		    s.add(pwl_07 >= (int)segLower + 1 && pwl_07 <= (int)segUpper);
		    
		    expr pwl_70 = c.int_const("pwl_70");
		    s.add(pwl_70 >= (int)segLower + 1 && pwl_70 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_07(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_07(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_70(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_70(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_07, t_after_07, implies(((t_before_07 < t_after_07) && (t_before_07 >= (int)segLower + 1) && (t_before_07 <= (int)segUpper) && (t_after_07 >= (int)segLower) && (t_after_07 <= (int)segUpper)), ((rho_07(t_before_07) < rho_07(t_after_07)) && (rho_70(t_before_07) < rho_70(t_after_07))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_7, implies(((rho_07(pred_0) == pred_7) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_0_x(pred_0)) * (a_7_x(pred_7) - a_0_x(pred_0))) + ((a_7_y(pred_7) - a_0_y(pred_0)) * (a_7_y(pred_7) - a_0_y(pred_0))) + ((a_7_z(pred_7) - a_0_z(pred_0)) * (a_7_z(pred_7) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_07, implies(((pwl_07 >= (int)segLower + 1) && (pwl_07 <= (int)segUpper)), (rho_primed_07(pwl_07) == rho_07(c.int_val(pwl_07)) + ((pwl_07 - c.int_val(pwl_07)) * (rho_07(c.int_val(pwl_07) + 1) - rho_07(c.int_val(pwl_07))))))));
			s.add(forall(pwl_70, implies(((pwl_70 >= (int)segLower + 1) && (pwl_70 <= (int)segUpper)), (rho_primed_70(pwl_70) == rho_70(c.int_val(pwl_70)) + ((pwl_70 - c.int_val(pwl_70)) * (rho_70(c.int_val(pwl_70) + 1) - rho_70(c.int_val(pwl_70))))))));
			
			//inverse re-timing
			s.add(forall(t_07, implies(((t_07 >= (int)segLower) && (t_07 <= (int)segUpper)), (rho_70(rho_07(t_07)) == t_07))));

			// ================ AGENT 0 AND AGENT 7 END ================ //
			
			// =============== AGENT 1 AND AGENT 2 START =============== //
			
			//agent pair smt variables
			expr t_12 = c.int_const("t_12");
		    s.add(t_12 >= (int)segLower + 1 && t_12 <= (int)segUpper);
		    
		    expr t_before_12 = c.int_const("t_before_12");
		    expr t_after_12 = c.int_const("t_after_12");
		    s.add(t_before_12 >= (int)segLower + 1 && t_before_12 <= (int)segUpper && t_after_12 >= (int)segLower && t_after_12 <= (int)segUpper);
		    
		    func_decl rho_12 = function("rho_12", c.int_sort(), c.int_sort());
		    func_decl rho_primed_12 = function("rho_primed_12", c.real_sort(), c.real_sort());
		    
		    func_decl rho_21 = function("rho_21", c.int_sort(), c.int_sort());
		    func_decl rho_primed_21 = function("rho_primed_21", c.real_sort(), c.real_sort());
		    
		    expr pwl_12 = c.int_const("pwl_12");
		    s.add(pwl_12 >= (int)segLower + 1 && pwl_12 <= (int)segUpper);
		    
		    expr pwl_21 = c.int_const("pwl_21");
		    s.add(pwl_21 >= (int)segLower + 1 && pwl_21 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_12(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_12(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_21(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_21(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_12, t_after_12, implies(((t_before_12 < t_after_12) && (t_before_12 >= (int)segLower + 1) && (t_before_12 <= (int)segUpper) && (t_after_12 >= (int)segLower) && (t_after_12 <= (int)segUpper)), ((rho_12(t_before_12) < rho_12(t_after_12)) && (rho_21(t_before_12) < rho_21(t_after_12))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_2, implies(((rho_12(pred_1) == pred_2) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_2 >= (int)segLower) && (pred_2 <= (int)segUpper)), (c.real_val(delta) <= (((a_2_x(pred_2) - a_1_x(pred_1)) * (a_2_x(pred_2) - a_1_x(pred_1))) + ((a_2_y(pred_2) - a_1_y(pred_1)) * (a_2_y(pred_2) - a_1_y(pred_1))) + ((a_2_z(pred_2) - a_1_z(pred_1)) * (a_2_z(pred_2) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_12, implies(((pwl_12 >= (int)segLower + 1) && (pwl_12 <= (int)segUpper)), (rho_primed_12(pwl_12) == rho_12(c.int_val(pwl_12)) + ((pwl_12 - c.int_val(pwl_12)) * (rho_12(c.int_val(pwl_12) + 1) - rho_12(c.int_val(pwl_12))))))));
			s.add(forall(pwl_21, implies(((pwl_21 >= (int)segLower + 1) && (pwl_21 <= (int)segUpper)), (rho_primed_21(pwl_21) == rho_21(c.int_val(pwl_21)) + ((pwl_21 - c.int_val(pwl_21)) * (rho_21(c.int_val(pwl_21) + 1) - rho_21(c.int_val(pwl_21))))))));
			
			//inverse re-timing
			s.add(forall(t_12, implies(((t_12 >= (int)segLower) && (t_12 <= (int)segUpper)), (rho_21(rho_12(t_12)) == t_12))));

			// ================ AGENT 1 AND AGENT 2 END ================ //
			
			// =============== AGENT 1 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_13 = c.int_const("t_13");
		    s.add(t_13 >= (int)segLower + 1 && t_13 <= (int)segUpper);
		    
		    expr t_before_13 = c.int_const("t_before_13");
		    expr t_after_13 = c.int_const("t_after_13");
		    s.add(t_before_13 >= (int)segLower + 1 && t_before_13 <= (int)segUpper && t_after_13 >= (int)segLower && t_after_13 <= (int)segUpper);
		    
		    func_decl rho_13 = function("rho_13", c.int_sort(), c.int_sort());
		    func_decl rho_primed_13 = function("rho_primed_13", c.real_sort(), c.real_sort());
		    
		    func_decl rho_31 = function("rho_31", c.int_sort(), c.int_sort());
		    func_decl rho_primed_31 = function("rho_primed_31", c.real_sort(), c.real_sort());
		    
		    expr pwl_13 = c.int_const("pwl_13");
		    s.add(pwl_13 >= (int)segLower + 1 && pwl_13 <= (int)segUpper);
		    
		    expr pwl_31 = c.int_const("pwl_31");
		    s.add(pwl_31 >= (int)segLower + 1 && pwl_31 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_13(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_13(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_31(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_31(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_13, t_after_13, implies(((t_before_13 < t_after_13) && (t_before_13 >= (int)segLower + 1) && (t_before_13 <= (int)segUpper) && (t_after_13 >= (int)segLower) && (t_after_13 <= (int)segUpper)), ((rho_13(t_before_13) < rho_13(t_after_13)) && (rho_31(t_before_13) < rho_31(t_after_13))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_3, implies(((rho_13(pred_1) == pred_3) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_1_x(pred_1)) * (a_3_x(pred_3) - a_1_x(pred_1))) + ((a_3_y(pred_3) - a_1_y(pred_1)) * (a_3_y(pred_3) - a_1_y(pred_1))) + ((a_3_z(pred_3) - a_1_z(pred_1)) * (a_3_z(pred_3) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_13, implies(((pwl_13 >= (int)segLower + 1) && (pwl_13 <= (int)segUpper)), (rho_primed_13(pwl_13) == rho_13(c.int_val(pwl_13)) + ((pwl_13 - c.int_val(pwl_13)) * (rho_13(c.int_val(pwl_13) + 1) - rho_13(c.int_val(pwl_13))))))));
			s.add(forall(pwl_31, implies(((pwl_31 >= (int)segLower + 1) && (pwl_31 <= (int)segUpper)), (rho_primed_31(pwl_31) == rho_31(c.int_val(pwl_31)) + ((pwl_31 - c.int_val(pwl_31)) * (rho_31(c.int_val(pwl_31) + 1) - rho_31(c.int_val(pwl_31))))))));
			
			//inverse re-timing
			s.add(forall(t_13, implies(((t_13 >= (int)segLower) && (t_13 <= (int)segUpper)), (rho_31(rho_13(t_13)) == t_13))));

			// ================ AGENT 1 AND AGENT 3 END ================ //
			
			// =============== AGENT 1 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_14 = c.int_const("t_14");
		    s.add(t_14 >= (int)segLower + 1 && t_14 <= (int)segUpper);
		    
		    expr t_before_14 = c.int_const("t_before_14");
		    expr t_after_14 = c.int_const("t_after_14");
		    s.add(t_before_14 >= (int)segLower + 1 && t_before_14 <= (int)segUpper && t_after_14 >= (int)segLower && t_after_14 <= (int)segUpper);
		    
		    func_decl rho_14 = function("rho_14", c.int_sort(), c.int_sort());
		    func_decl rho_primed_14 = function("rho_primed_14", c.real_sort(), c.real_sort());
		    
		    func_decl rho_41 = function("rho_41", c.int_sort(), c.int_sort());
		    func_decl rho_primed_41 = function("rho_primed_41", c.real_sort(), c.real_sort());
		    
		    expr pwl_14 = c.int_const("pwl_14");
		    s.add(pwl_14 >= (int)segLower + 1 && pwl_14 <= (int)segUpper);
		    
		    expr pwl_41 = c.int_const("pwl_41");
		    s.add(pwl_41 >= (int)segLower + 1 && pwl_41 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_14(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_14(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_41(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_41(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_14, t_after_14, implies(((t_before_14 < t_after_14) && (t_before_14 >= (int)segLower + 1) && (t_before_14 <= (int)segUpper) && (t_after_14 >= (int)segLower) && (t_after_14 <= (int)segUpper)), ((rho_14(t_before_14) < rho_14(t_after_14)) && (rho_41(t_before_14) < rho_41(t_after_14))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_4, implies(((rho_14(pred_1) == pred_4) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_1_x(pred_1)) * (a_4_x(pred_4) - a_1_x(pred_1))) + ((a_4_y(pred_4) - a_1_y(pred_1)) * (a_4_y(pred_4) - a_1_y(pred_1))) + ((a_4_z(pred_4) - a_1_z(pred_1)) * (a_4_z(pred_4) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_14, implies(((pwl_14 >= (int)segLower + 1) && (pwl_14 <= (int)segUpper)), (rho_primed_14(pwl_14) == rho_14(c.int_val(pwl_14)) + ((pwl_14 - c.int_val(pwl_14)) * (rho_14(c.int_val(pwl_14) + 1) - rho_14(c.int_val(pwl_14))))))));
			s.add(forall(pwl_41, implies(((pwl_41 >= (int)segLower + 1) && (pwl_41 <= (int)segUpper)), (rho_primed_41(pwl_41) == rho_41(c.int_val(pwl_41)) + ((pwl_41 - c.int_val(pwl_41)) * (rho_41(c.int_val(pwl_41) + 1) - rho_41(c.int_val(pwl_41))))))));
			
			//inverse re-timing
			s.add(forall(t_14, implies(((t_14 >= (int)segLower) && (t_14 <= (int)segUpper)), (rho_41(rho_14(t_14)) == t_14))));

			// ================ AGENT 1 AND AGENT 4 END ================ //
			
			// =============== AGENT 1 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_15 = c.int_const("t_15");
		    s.add(t_15 >= (int)segLower + 1 && t_15 <= (int)segUpper);
		    
		    expr t_before_15 = c.int_const("t_before_15");
		    expr t_after_15 = c.int_const("t_after_15");
		    s.add(t_before_15 >= (int)segLower + 1 && t_before_15 <= (int)segUpper && t_after_15 >= (int)segLower && t_after_15 <= (int)segUpper);
		    
		    func_decl rho_15 = function("rho_15", c.int_sort(), c.int_sort());
		    func_decl rho_primed_15 = function("rho_primed_15", c.real_sort(), c.real_sort());
		    
		    func_decl rho_51 = function("rho_51", c.int_sort(), c.int_sort());
		    func_decl rho_primed_51 = function("rho_primed_51", c.real_sort(), c.real_sort());
		    
		    expr pwl_15 = c.int_const("pwl_15");
		    s.add(pwl_15 >= (int)segLower + 1 && pwl_15 <= (int)segUpper);
		    
		    expr pwl_51 = c.int_const("pwl_51");
		    s.add(pwl_51 >= (int)segLower + 1 && pwl_51 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_15(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_15(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_51(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_51(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_15, t_after_15, implies(((t_before_15 < t_after_15) && (t_before_15 >= (int)segLower + 1) && (t_before_15 <= (int)segUpper) && (t_after_15 >= (int)segLower) && (t_after_15 <= (int)segUpper)), ((rho_15(t_before_15) < rho_15(t_after_15)) && (rho_51(t_before_15) < rho_51(t_after_15))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_5, implies(((rho_15(pred_1) == pred_5) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_1_x(pred_1)) * (a_5_x(pred_5) - a_1_x(pred_1))) + ((a_5_y(pred_5) - a_1_y(pred_1)) * (a_5_y(pred_5) - a_1_y(pred_1))) + ((a_5_z(pred_5) - a_1_z(pred_1)) * (a_5_z(pred_5) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_15, implies(((pwl_15 >= (int)segLower + 1) && (pwl_15 <= (int)segUpper)), (rho_primed_15(pwl_15) == rho_15(c.int_val(pwl_15)) + ((pwl_15 - c.int_val(pwl_15)) * (rho_15(c.int_val(pwl_15) + 1) - rho_15(c.int_val(pwl_15))))))));
			s.add(forall(pwl_51, implies(((pwl_51 >= (int)segLower + 1) && (pwl_51 <= (int)segUpper)), (rho_primed_51(pwl_51) == rho_51(c.int_val(pwl_51)) + ((pwl_51 - c.int_val(pwl_51)) * (rho_51(c.int_val(pwl_51) + 1) - rho_51(c.int_val(pwl_51))))))));
			
			//inverse re-timing
			s.add(forall(t_15, implies(((t_15 >= (int)segLower) && (t_15 <= (int)segUpper)), (rho_51(rho_15(t_15)) == t_15))));

			// ================ AGENT 1 AND AGENT 5 END ================ //
			
			// =============== AGENT 1 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_16 = c.int_const("t_16");
		    s.add(t_16 >= (int)segLower + 1 && t_16 <= (int)segUpper);
		    
		    expr t_before_16 = c.int_const("t_before_16");
		    expr t_after_16 = c.int_const("t_after_16");
		    s.add(t_before_16 >= (int)segLower + 1 && t_before_16 <= (int)segUpper && t_after_16 >= (int)segLower && t_after_16 <= (int)segUpper);
		    
		    func_decl rho_16 = function("rho_16", c.int_sort(), c.int_sort());
		    func_decl rho_primed_16 = function("rho_primed_16", c.real_sort(), c.real_sort());
		    
		    func_decl rho_61 = function("rho_61", c.int_sort(), c.int_sort());
		    func_decl rho_primed_61 = function("rho_primed_61", c.real_sort(), c.real_sort());
		    
		    expr pwl_16 = c.int_const("pwl_16");
		    s.add(pwl_16 >= (int)segLower + 1 && pwl_16 <= (int)segUpper);
		    
		    expr pwl_61 = c.int_const("pwl_61");
		    s.add(pwl_61 >= (int)segLower + 1 && pwl_61 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_16(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_16(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_61(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_61(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_16, t_after_16, implies(((t_before_16 < t_after_16) && (t_before_16 >= (int)segLower + 1) && (t_before_16 <= (int)segUpper) && (t_after_16 >= (int)segLower) && (t_after_16 <= (int)segUpper)), ((rho_16(t_before_16) < rho_16(t_after_16)) && (rho_61(t_before_16) < rho_61(t_after_16))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_6, implies(((rho_16(pred_1) == pred_6) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_1_x(pred_1)) * (a_6_x(pred_6) - a_1_x(pred_1))) + ((a_6_y(pred_6) - a_1_y(pred_1)) * (a_6_y(pred_6) - a_1_y(pred_1))) + ((a_6_z(pred_6) - a_1_z(pred_1)) * (a_6_z(pred_6) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_16, implies(((pwl_16 >= (int)segLower + 1) && (pwl_16 <= (int)segUpper)), (rho_primed_16(pwl_16) == rho_16(c.int_val(pwl_16)) + ((pwl_16 - c.int_val(pwl_16)) * (rho_16(c.int_val(pwl_16) + 1) - rho_16(c.int_val(pwl_16))))))));
			s.add(forall(pwl_61, implies(((pwl_61 >= (int)segLower + 1) && (pwl_61 <= (int)segUpper)), (rho_primed_61(pwl_61) == rho_61(c.int_val(pwl_61)) + ((pwl_61 - c.int_val(pwl_61)) * (rho_61(c.int_val(pwl_61) + 1) - rho_61(c.int_val(pwl_61))))))));
			
			//inverse re-timing
			s.add(forall(t_16, implies(((t_16 >= (int)segLower) && (t_16 <= (int)segUpper)), (rho_61(rho_16(t_16)) == t_16))));

			// ================ AGENT 1 AND AGENT 6 END ================ //
			
			// =============== AGENT 1 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_17 = c.int_const("t_17");
		    s.add(t_17 >= (int)segLower + 1 && t_17 <= (int)segUpper);
		    
		    expr t_before_17 = c.int_const("t_before_17");
		    expr t_after_17 = c.int_const("t_after_17");
		    s.add(t_before_17 >= (int)segLower + 1 && t_before_17 <= (int)segUpper && t_after_17 >= (int)segLower && t_after_17 <= (int)segUpper);
		    
		    func_decl rho_17 = function("rho_17", c.int_sort(), c.int_sort());
		    func_decl rho_primed_17 = function("rho_primed_17", c.real_sort(), c.real_sort());
		    
		    func_decl rho_71 = function("rho_71", c.int_sort(), c.int_sort());
		    func_decl rho_primed_71 = function("rho_primed_71", c.real_sort(), c.real_sort());
		    
		    expr pwl_17 = c.int_const("pwl_17");
		    s.add(pwl_17 >= (int)segLower + 1 && pwl_17 <= (int)segUpper);
		    
		    expr pwl_71 = c.int_const("pwl_71");
		    s.add(pwl_71 >= (int)segLower + 1 && pwl_71 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_17(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_17(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_71(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_71(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_17, t_after_17, implies(((t_before_17 < t_after_17) && (t_before_17 >= (int)segLower + 1) && (t_before_17 <= (int)segUpper) && (t_after_17 >= (int)segLower) && (t_after_17 <= (int)segUpper)), ((rho_17(t_before_17) < rho_17(t_after_17)) && (rho_71(t_before_17) < rho_71(t_after_17))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_7, implies(((rho_17(pred_1) == pred_7) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_1_x(pred_1)) * (a_7_x(pred_7) - a_1_x(pred_1))) + ((a_7_y(pred_7) - a_1_y(pred_1)) * (a_7_y(pred_7) - a_1_y(pred_1))) + ((a_7_z(pred_7) - a_1_z(pred_1)) * (a_7_z(pred_7) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_17, implies(((pwl_17 >= (int)segLower + 1) && (pwl_17 <= (int)segUpper)), (rho_primed_17(pwl_17) == rho_17(c.int_val(pwl_17)) + ((pwl_17 - c.int_val(pwl_17)) * (rho_17(c.int_val(pwl_17) + 1) - rho_17(c.int_val(pwl_17))))))));
			s.add(forall(pwl_71, implies(((pwl_71 >= (int)segLower + 1) && (pwl_71 <= (int)segUpper)), (rho_primed_71(pwl_71) == rho_71(c.int_val(pwl_71)) + ((pwl_71 - c.int_val(pwl_71)) * (rho_71(c.int_val(pwl_71) + 1) - rho_71(c.int_val(pwl_71))))))));
			
			//inverse re-timing
			s.add(forall(t_17, implies(((t_17 >= (int)segLower) && (t_17 <= (int)segUpper)), (rho_71(rho_17(t_17)) == t_17))));

			// ================ AGENT 1 AND AGENT 7 END ================ //
			
			// =============== AGENT 2 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_23 = c.int_const("t_23");
		    s.add(t_23 >= (int)segLower + 1 && t_23 <= (int)segUpper);
		    
		    expr t_before_23 = c.int_const("t_before_23");
		    expr t_after_23 = c.int_const("t_after_23");
		    s.add(t_before_23 >= (int)segLower + 1 && t_before_23 <= (int)segUpper && t_after_23 >= (int)segLower && t_after_23 <= (int)segUpper);
		    
		    func_decl rho_23 = function("rho_23", c.int_sort(), c.int_sort());
		    func_decl rho_primed_23 = function("rho_primed_23", c.real_sort(), c.real_sort());
		    
		    func_decl rho_32 = function("rho_32", c.int_sort(), c.int_sort());
		    func_decl rho_primed_32 = function("rho_primed_32", c.real_sort(), c.real_sort());
		    
		    expr pwl_23 = c.int_const("pwl_23");
		    s.add(pwl_23 >= (int)segLower + 1 && pwl_23 <= (int)segUpper);
		    
		    expr pwl_32 = c.int_const("pwl_32");
		    s.add(pwl_32 >= (int)segLower + 1 && pwl_32 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_23(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_23(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_32(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_32(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_23, t_after_23, implies(((t_before_23 < t_after_23) && (t_before_23 >= (int)segLower + 1) && (t_before_23 <= (int)segUpper) && (t_after_23 >= (int)segLower) && (t_after_23 <= (int)segUpper)), ((rho_23(t_before_23) < rho_23(t_after_23)) && (rho_32(t_before_23) < rho_32(t_after_23))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_3, implies(((rho_23(pred_2) == pred_3) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_2_x(pred_2)) * (a_3_x(pred_3) - a_2_x(pred_2))) + ((a_3_y(pred_3) - a_2_y(pred_2)) * (a_3_y(pred_3) - a_2_y(pred_2))) + ((a_3_z(pred_3) - a_2_z(pred_2)) * (a_3_z(pred_3) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_23, implies(((pwl_23 >= (int)segLower + 1) && (pwl_23 <= (int)segUpper)), (rho_primed_23(pwl_23) == rho_23(c.int_val(pwl_23)) + ((pwl_23 - c.int_val(pwl_23)) * (rho_23(c.int_val(pwl_23) + 1) - rho_23(c.int_val(pwl_23))))))));
			s.add(forall(pwl_32, implies(((pwl_32 >= (int)segLower + 1) && (pwl_32 <= (int)segUpper)), (rho_primed_32(pwl_32) == rho_32(c.int_val(pwl_32)) + ((pwl_32 - c.int_val(pwl_32)) * (rho_32(c.int_val(pwl_32) + 1) - rho_32(c.int_val(pwl_32))))))));
			
			//inverse re-timing
			s.add(forall(t_23, implies(((t_23 >= (int)segLower) && (t_23 <= (int)segUpper)), (rho_32(rho_23(t_23)) == t_23))));

			// ================ AGENT 2 AND AGENT 3 END ================ //
			
			// =============== AGENT 2 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_24 = c.int_const("t_24");
		    s.add(t_24 >= (int)segLower + 1 && t_24 <= (int)segUpper);
		    
		    expr t_before_24 = c.int_const("t_before_24");
		    expr t_after_24 = c.int_const("t_after_24");
		    s.add(t_before_24 >= (int)segLower + 1 && t_before_24 <= (int)segUpper && t_after_24 >= (int)segLower && t_after_24 <= (int)segUpper);
		    
		    func_decl rho_24 = function("rho_24", c.int_sort(), c.int_sort());
		    func_decl rho_primed_24 = function("rho_primed_24", c.real_sort(), c.real_sort());
		    
		    func_decl rho_42 = function("rho_42", c.int_sort(), c.int_sort());
		    func_decl rho_primed_42 = function("rho_primed_42", c.real_sort(), c.real_sort());
		    
		    expr pwl_24 = c.int_const("pwl_24");
		    s.add(pwl_24 >= (int)segLower + 1 && pwl_24 <= (int)segUpper);
		    
		    expr pwl_42 = c.int_const("pwl_42");
		    s.add(pwl_42 >= (int)segLower + 1 && pwl_42 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_24(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_24(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_42(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_42(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_24, t_after_24, implies(((t_before_24 < t_after_24) && (t_before_24 >= (int)segLower + 1) && (t_before_24 <= (int)segUpper) && (t_after_24 >= (int)segLower) && (t_after_24 <= (int)segUpper)), ((rho_24(t_before_24) < rho_24(t_after_24)) && (rho_42(t_before_24) < rho_42(t_after_24))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_4, implies(((rho_24(pred_2) == pred_4) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_2_x(pred_2)) * (a_4_x(pred_4) - a_2_x(pred_2))) + ((a_4_y(pred_4) - a_2_y(pred_2)) * (a_4_y(pred_4) - a_2_y(pred_2))) + ((a_4_z(pred_4) - a_2_z(pred_2)) * (a_4_z(pred_4) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_24, implies(((pwl_24 >= (int)segLower + 1) && (pwl_24 <= (int)segUpper)), (rho_primed_24(pwl_24) == rho_24(c.int_val(pwl_24)) + ((pwl_24 - c.int_val(pwl_24)) * (rho_24(c.int_val(pwl_24) + 1) - rho_24(c.int_val(pwl_24))))))));
			s.add(forall(pwl_42, implies(((pwl_42 >= (int)segLower + 1) && (pwl_42 <= (int)segUpper)), (rho_primed_42(pwl_42) == rho_42(c.int_val(pwl_42)) + ((pwl_42 - c.int_val(pwl_42)) * (rho_42(c.int_val(pwl_42) + 1) - rho_42(c.int_val(pwl_42))))))));
			
			//inverse re-timing
			s.add(forall(t_24, implies(((t_24 >= (int)segLower) && (t_24 <= (int)segUpper)), (rho_42(rho_24(t_24)) == t_24))));

			// ================ AGENT 2 AND AGENT 4 END ================ //
			
			// =============== AGENT 2 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_25 = c.int_const("t_25");
		    s.add(t_25 >= (int)segLower + 1 && t_25 <= (int)segUpper);
		    
		    expr t_before_25 = c.int_const("t_before_25");
		    expr t_after_25 = c.int_const("t_after_25");
		    s.add(t_before_25 >= (int)segLower + 1 && t_before_25 <= (int)segUpper && t_after_25 >= (int)segLower && t_after_25 <= (int)segUpper);
		    
		    func_decl rho_25 = function("rho_25", c.int_sort(), c.int_sort());
		    func_decl rho_primed_25 = function("rho_primed_25", c.real_sort(), c.real_sort());
		    
		    func_decl rho_52 = function("rho_52", c.int_sort(), c.int_sort());
		    func_decl rho_primed_52 = function("rho_primed_52", c.real_sort(), c.real_sort());
		    
		    expr pwl_25 = c.int_const("pwl_25");
		    s.add(pwl_25 >= (int)segLower + 1 && pwl_25 <= (int)segUpper);
		    
		    expr pwl_52 = c.int_const("pwl_52");
		    s.add(pwl_52 >= (int)segLower + 1 && pwl_52 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_25(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_25(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_52(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_52(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_25, t_after_25, implies(((t_before_25 < t_after_25) && (t_before_25 >= (int)segLower + 1) && (t_before_25 <= (int)segUpper) && (t_after_25 >= (int)segLower) && (t_after_25 <= (int)segUpper)), ((rho_25(t_before_25) < rho_25(t_after_25)) && (rho_52(t_before_25) < rho_52(t_after_25))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_5, implies(((rho_25(pred_2) == pred_5) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_2_x(pred_2)) * (a_5_x(pred_5) - a_2_x(pred_2))) + ((a_5_y(pred_5) - a_2_y(pred_2)) * (a_5_y(pred_5) - a_2_y(pred_2))) + ((a_5_z(pred_5) - a_2_z(pred_2)) * (a_5_z(pred_5) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_25, implies(((pwl_25 >= (int)segLower + 1) && (pwl_25 <= (int)segUpper)), (rho_primed_25(pwl_25) == rho_25(c.int_val(pwl_25)) + ((pwl_25 - c.int_val(pwl_25)) * (rho_25(c.int_val(pwl_25) + 1) - rho_25(c.int_val(pwl_25))))))));
			s.add(forall(pwl_52, implies(((pwl_52 >= (int)segLower + 1) && (pwl_52 <= (int)segUpper)), (rho_primed_52(pwl_52) == rho_52(c.int_val(pwl_52)) + ((pwl_52 - c.int_val(pwl_52)) * (rho_52(c.int_val(pwl_52) + 1) - rho_52(c.int_val(pwl_52))))))));
			
			//inverse re-timing
			s.add(forall(t_25, implies(((t_25 >= (int)segLower) && (t_25 <= (int)segUpper)), (rho_52(rho_25(t_25)) == t_25))));

			// ================ AGENT 2 AND AGENT 5 END ================ //
			
			// =============== AGENT 2 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_26 = c.int_const("t_26");
		    s.add(t_26 >= (int)segLower + 1 && t_26 <= (int)segUpper);
		    
		    expr t_before_26 = c.int_const("t_before_26");
		    expr t_after_26 = c.int_const("t_after_26");
		    s.add(t_before_26 >= (int)segLower + 1 && t_before_26 <= (int)segUpper && t_after_26 >= (int)segLower && t_after_26 <= (int)segUpper);
		    
		    func_decl rho_26 = function("rho_26", c.int_sort(), c.int_sort());
		    func_decl rho_primed_26 = function("rho_primed_26", c.real_sort(), c.real_sort());
		    
		    func_decl rho_62 = function("rho_62", c.int_sort(), c.int_sort());
		    func_decl rho_primed_62 = function("rho_primed_62", c.real_sort(), c.real_sort());
		    
		    expr pwl_26 = c.int_const("pwl_26");
		    s.add(pwl_26 >= (int)segLower + 1 && pwl_26 <= (int)segUpper);
		    
		    expr pwl_62 = c.int_const("pwl_62");
		    s.add(pwl_62 >= (int)segLower + 1 && pwl_62 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_26(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_26(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_62(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_62(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_26, t_after_26, implies(((t_before_26 < t_after_26) && (t_before_26 >= (int)segLower + 1) && (t_before_26 <= (int)segUpper) && (t_after_26 >= (int)segLower) && (t_after_26 <= (int)segUpper)), ((rho_26(t_before_26) < rho_26(t_after_26)) && (rho_62(t_before_26) < rho_62(t_after_26))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_6, implies(((rho_26(pred_2) == pred_6) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_2_x(pred_2)) * (a_6_x(pred_6) - a_2_x(pred_2))) + ((a_6_y(pred_6) - a_2_y(pred_2)) * (a_6_y(pred_6) - a_2_y(pred_2))) + ((a_6_z(pred_6) - a_2_z(pred_2)) * (a_6_z(pred_6) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_26, implies(((pwl_26 >= (int)segLower + 1) && (pwl_26 <= (int)segUpper)), (rho_primed_26(pwl_26) == rho_26(c.int_val(pwl_26)) + ((pwl_26 - c.int_val(pwl_26)) * (rho_26(c.int_val(pwl_26) + 1) - rho_26(c.int_val(pwl_26))))))));
			s.add(forall(pwl_62, implies(((pwl_62 >= (int)segLower + 1) && (pwl_62 <= (int)segUpper)), (rho_primed_62(pwl_62) == rho_62(c.int_val(pwl_62)) + ((pwl_62 - c.int_val(pwl_62)) * (rho_62(c.int_val(pwl_62) + 1) - rho_62(c.int_val(pwl_62))))))));
			
			//inverse re-timing
			s.add(forall(t_26, implies(((t_26 >= (int)segLower) && (t_26 <= (int)segUpper)), (rho_62(rho_26(t_26)) == t_26))));

			// ================ AGENT 2 AND AGENT 6 END ================ //
			
			// =============== AGENT 2 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_27 = c.int_const("t_27");
		    s.add(t_27 >= (int)segLower + 1 && t_27 <= (int)segUpper);
		    
		    expr t_before_27 = c.int_const("t_before_27");
		    expr t_after_27 = c.int_const("t_after_27");
		    s.add(t_before_27 >= (int)segLower + 1 && t_before_27 <= (int)segUpper && t_after_27 >= (int)segLower && t_after_27 <= (int)segUpper);
		    
		    func_decl rho_27 = function("rho_27", c.int_sort(), c.int_sort());
		    func_decl rho_primed_27 = function("rho_primed_27", c.real_sort(), c.real_sort());
		    
		    func_decl rho_72 = function("rho_72", c.int_sort(), c.int_sort());
		    func_decl rho_primed_72 = function("rho_primed_72", c.real_sort(), c.real_sort());
		    
		    expr pwl_27 = c.int_const("pwl_27");
		    s.add(pwl_27 >= (int)segLower + 1 && pwl_27 <= (int)segUpper);
		    
		    expr pwl_72 = c.int_const("pwl_72");
		    s.add(pwl_72 >= (int)segLower + 1 && pwl_72 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_27(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_27(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_72(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_72(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_27, t_after_27, implies(((t_before_27 < t_after_27) && (t_before_27 >= (int)segLower + 1) && (t_before_27 <= (int)segUpper) && (t_after_27 >= (int)segLower) && (t_after_27 <= (int)segUpper)), ((rho_27(t_before_27) < rho_27(t_after_27)) && (rho_72(t_before_27) < rho_72(t_after_27))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_7, implies(((rho_27(pred_2) == pred_7) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_2_x(pred_2)) * (a_7_x(pred_7) - a_2_x(pred_2))) + ((a_7_y(pred_7) - a_2_y(pred_2)) * (a_7_y(pred_7) - a_2_y(pred_2))) + ((a_7_z(pred_7) - a_2_z(pred_2)) * (a_7_z(pred_7) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_27, implies(((pwl_27 >= (int)segLower + 1) && (pwl_27 <= (int)segUpper)), (rho_primed_27(pwl_27) == rho_27(c.int_val(pwl_27)) + ((pwl_27 - c.int_val(pwl_27)) * (rho_27(c.int_val(pwl_27) + 1) - rho_27(c.int_val(pwl_27))))))));
			s.add(forall(pwl_72, implies(((pwl_72 >= (int)segLower + 1) && (pwl_72 <= (int)segUpper)), (rho_primed_72(pwl_72) == rho_72(c.int_val(pwl_72)) + ((pwl_72 - c.int_val(pwl_72)) * (rho_72(c.int_val(pwl_72) + 1) - rho_72(c.int_val(pwl_72))))))));
			
			//inverse re-timing
			s.add(forall(t_27, implies(((t_27 >= (int)segLower) && (t_27 <= (int)segUpper)), (rho_72(rho_27(t_27)) == t_27))));

			// ================ AGENT 2 AND AGENT 7 END ================ //
			
			// =============== AGENT 3 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_34 = c.int_const("t_34");
		    s.add(t_34 >= (int)segLower + 1 && t_34 <= (int)segUpper);
		    
		    expr t_before_34 = c.int_const("t_before_34");
		    expr t_after_34 = c.int_const("t_after_34");
		    s.add(t_before_34 >= (int)segLower + 1 && t_before_34 <= (int)segUpper && t_after_34 >= (int)segLower && t_after_34 <= (int)segUpper);
		    
		    func_decl rho_34 = function("rho_34", c.int_sort(), c.int_sort());
		    func_decl rho_primed_34 = function("rho_primed_34", c.real_sort(), c.real_sort());
		    
		    func_decl rho_43 = function("rho_43", c.int_sort(), c.int_sort());
		    func_decl rho_primed_43 = function("rho_primed_43", c.real_sort(), c.real_sort());
		    
		    expr pwl_34 = c.int_const("pwl_34");
		    s.add(pwl_34 >= (int)segLower + 1 && pwl_34 <= (int)segUpper);
		    
		    expr pwl_43 = c.int_const("pwl_43");
		    s.add(pwl_43 >= (int)segLower + 1 && pwl_43 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_34(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_34(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_43(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_43(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_34, t_after_34, implies(((t_before_34 < t_after_34) && (t_before_34 >= (int)segLower + 1) && (t_before_34 <= (int)segUpper) && (t_after_34 >= (int)segLower) && (t_after_34 <= (int)segUpper)), ((rho_34(t_before_34) < rho_34(t_after_34)) && (rho_43(t_before_34) < rho_43(t_after_34))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_4, implies(((rho_34(pred_3) == pred_4) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_3_x(pred_3)) * (a_4_x(pred_4) - a_3_x(pred_3))) + ((a_4_y(pred_4) - a_3_y(pred_3)) * (a_4_y(pred_4) - a_3_y(pred_3))) + ((a_4_z(pred_4) - a_3_z(pred_3)) * (a_4_z(pred_4) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_34, implies(((pwl_34 >= (int)segLower + 1) && (pwl_34 <= (int)segUpper)), (rho_primed_34(pwl_34) == rho_34(c.int_val(pwl_34)) + ((pwl_34 - c.int_val(pwl_34)) * (rho_34(c.int_val(pwl_34) + 1) - rho_34(c.int_val(pwl_34))))))));
			s.add(forall(pwl_43, implies(((pwl_43 >= (int)segLower + 1) && (pwl_43 <= (int)segUpper)), (rho_primed_43(pwl_43) == rho_43(c.int_val(pwl_43)) + ((pwl_43 - c.int_val(pwl_43)) * (rho_43(c.int_val(pwl_43) + 1) - rho_43(c.int_val(pwl_43))))))));
			
			//inverse re-timing
			s.add(forall(t_34, implies(((t_34 >= (int)segLower) && (t_34 <= (int)segUpper)), (rho_43(rho_34(t_34)) == t_34))));

			// ================ AGENT 3 AND AGENT 4 END ================ //
			
			// =============== AGENT 3 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_35 = c.int_const("t_35");
		    s.add(t_35 >= (int)segLower + 1 && t_35 <= (int)segUpper);
		    
		    expr t_before_35 = c.int_const("t_before_35");
		    expr t_after_35 = c.int_const("t_after_35");
		    s.add(t_before_35 >= (int)segLower + 1 && t_before_35 <= (int)segUpper && t_after_35 >= (int)segLower && t_after_35 <= (int)segUpper);
		    
		    func_decl rho_35 = function("rho_35", c.int_sort(), c.int_sort());
		    func_decl rho_primed_35 = function("rho_primed_35", c.real_sort(), c.real_sort());
		    
		    func_decl rho_53 = function("rho_53", c.int_sort(), c.int_sort());
		    func_decl rho_primed_53 = function("rho_primed_53", c.real_sort(), c.real_sort());
		    
		    expr pwl_35 = c.int_const("pwl_35");
		    s.add(pwl_35 >= (int)segLower + 1 && pwl_35 <= (int)segUpper);
		    
		    expr pwl_53 = c.int_const("pwl_53");
		    s.add(pwl_53 >= (int)segLower + 1 && pwl_53 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_35(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_35(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_53(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_53(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_35, t_after_35, implies(((t_before_35 < t_after_35) && (t_before_35 >= (int)segLower + 1) && (t_before_35 <= (int)segUpper) && (t_after_35 >= (int)segLower) && (t_after_35 <= (int)segUpper)), ((rho_35(t_before_35) < rho_35(t_after_35)) && (rho_53(t_before_35) < rho_53(t_after_35))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_5, implies(((rho_35(pred_3) == pred_5) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_3_x(pred_3)) * (a_5_x(pred_5) - a_3_x(pred_3))) + ((a_5_y(pred_5) - a_3_y(pred_3)) * (a_5_y(pred_5) - a_3_y(pred_3))) + ((a_5_z(pred_5) - a_3_z(pred_3)) * (a_5_z(pred_5) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_35, implies(((pwl_35 >= (int)segLower + 1) && (pwl_35 <= (int)segUpper)), (rho_primed_35(pwl_35) == rho_35(c.int_val(pwl_35)) + ((pwl_35 - c.int_val(pwl_35)) * (rho_35(c.int_val(pwl_35) + 1) - rho_35(c.int_val(pwl_35))))))));
			s.add(forall(pwl_53, implies(((pwl_53 >= (int)segLower + 1) && (pwl_53 <= (int)segUpper)), (rho_primed_53(pwl_53) == rho_53(c.int_val(pwl_53)) + ((pwl_53 - c.int_val(pwl_53)) * (rho_53(c.int_val(pwl_53) + 1) - rho_53(c.int_val(pwl_53))))))));
			
			//inverse re-timing
			s.add(forall(t_35, implies(((t_35 >= (int)segLower) && (t_35 <= (int)segUpper)), (rho_53(rho_35(t_35)) == t_35))));

			// ================ AGENT 3 AND AGENT 5 END ================ //
			
			// =============== AGENT 3 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_36 = c.int_const("t_36");
		    s.add(t_36 >= (int)segLower + 1 && t_36 <= (int)segUpper);
		    
		    expr t_before_36 = c.int_const("t_before_36");
		    expr t_after_36 = c.int_const("t_after_36");
		    s.add(t_before_36 >= (int)segLower + 1 && t_before_36 <= (int)segUpper && t_after_36 >= (int)segLower && t_after_36 <= (int)segUpper);
		    
		    func_decl rho_36 = function("rho_36", c.int_sort(), c.int_sort());
		    func_decl rho_primed_36 = function("rho_primed_36", c.real_sort(), c.real_sort());
		    
		    func_decl rho_63 = function("rho_63", c.int_sort(), c.int_sort());
		    func_decl rho_primed_63 = function("rho_primed_63", c.real_sort(), c.real_sort());
		    
		    expr pwl_36 = c.int_const("pwl_36");
		    s.add(pwl_36 >= (int)segLower + 1 && pwl_36 <= (int)segUpper);
		    
		    expr pwl_63 = c.int_const("pwl_63");
		    s.add(pwl_63 >= (int)segLower + 1 && pwl_63 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_36(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_36(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_63(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_63(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_36, t_after_36, implies(((t_before_36 < t_after_36) && (t_before_36 >= (int)segLower + 1) && (t_before_36 <= (int)segUpper) && (t_after_36 >= (int)segLower) && (t_after_36 <= (int)segUpper)), ((rho_36(t_before_36) < rho_36(t_after_36)) && (rho_63(t_before_36) < rho_63(t_after_36))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_6, implies(((rho_36(pred_3) == pred_6) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_3_x(pred_3)) * (a_6_x(pred_6) - a_3_x(pred_3))) + ((a_6_y(pred_6) - a_3_y(pred_3)) * (a_6_y(pred_6) - a_3_y(pred_3))) + ((a_6_z(pred_6) - a_3_z(pred_3)) * (a_6_z(pred_6) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_36, implies(((pwl_36 >= (int)segLower + 1) && (pwl_36 <= (int)segUpper)), (rho_primed_36(pwl_36) == rho_36(c.int_val(pwl_36)) + ((pwl_36 - c.int_val(pwl_36)) * (rho_36(c.int_val(pwl_36) + 1) - rho_36(c.int_val(pwl_36))))))));
			s.add(forall(pwl_63, implies(((pwl_63 >= (int)segLower + 1) && (pwl_63 <= (int)segUpper)), (rho_primed_63(pwl_63) == rho_63(c.int_val(pwl_63)) + ((pwl_63 - c.int_val(pwl_63)) * (rho_63(c.int_val(pwl_63) + 1) - rho_63(c.int_val(pwl_63))))))));
			
			//inverse re-timing
			s.add(forall(t_36, implies(((t_36 >= (int)segLower) && (t_36 <= (int)segUpper)), (rho_63(rho_36(t_36)) == t_36))));

			// ================ AGENT 3 AND AGENT 6 END ================ //
			
			// =============== AGENT 3 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_37 = c.int_const("t_37");
		    s.add(t_37 >= (int)segLower + 1 && t_37 <= (int)segUpper);
		    
		    expr t_before_37 = c.int_const("t_before_37");
		    expr t_after_37 = c.int_const("t_after_37");
		    s.add(t_before_37 >= (int)segLower + 1 && t_before_37 <= (int)segUpper && t_after_37 >= (int)segLower && t_after_37 <= (int)segUpper);
		    
		    func_decl rho_37 = function("rho_37", c.int_sort(), c.int_sort());
		    func_decl rho_primed_37 = function("rho_primed_37", c.real_sort(), c.real_sort());
		    
		    func_decl rho_73 = function("rho_73", c.int_sort(), c.int_sort());
		    func_decl rho_primed_73 = function("rho_primed_73", c.real_sort(), c.real_sort());
		    
		    expr pwl_37 = c.int_const("pwl_37");
		    s.add(pwl_37 >= (int)segLower + 1 && pwl_37 <= (int)segUpper);
		    
		    expr pwl_73 = c.int_const("pwl_73");
		    s.add(pwl_73 >= (int)segLower + 1 && pwl_73 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_37(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_37(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_73(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_73(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_37, t_after_37, implies(((t_before_37 < t_after_37) && (t_before_37 >= (int)segLower + 1) && (t_before_37 <= (int)segUpper) && (t_after_37 >= (int)segLower) && (t_after_37 <= (int)segUpper)), ((rho_37(t_before_37) < rho_37(t_after_37)) && (rho_73(t_before_37) < rho_73(t_after_37))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_7, implies(((rho_37(pred_3) == pred_7) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_3_x(pred_3)) * (a_7_x(pred_7) - a_3_x(pred_3))) + ((a_7_y(pred_7) - a_3_y(pred_3)) * (a_7_y(pred_7) - a_3_y(pred_3))) + ((a_7_z(pred_7) - a_3_z(pred_3)) * (a_7_z(pred_7) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_37, implies(((pwl_37 >= (int)segLower + 1) && (pwl_37 <= (int)segUpper)), (rho_primed_37(pwl_37) == rho_37(c.int_val(pwl_37)) + ((pwl_37 - c.int_val(pwl_37)) * (rho_37(c.int_val(pwl_37) + 1) - rho_37(c.int_val(pwl_37))))))));
			s.add(forall(pwl_73, implies(((pwl_73 >= (int)segLower + 1) && (pwl_73 <= (int)segUpper)), (rho_primed_73(pwl_73) == rho_73(c.int_val(pwl_73)) + ((pwl_73 - c.int_val(pwl_73)) * (rho_73(c.int_val(pwl_73) + 1) - rho_73(c.int_val(pwl_73))))))));
			
			//inverse re-timing
			s.add(forall(t_37, implies(((t_37 >= (int)segLower) && (t_37 <= (int)segUpper)), (rho_73(rho_37(t_37)) == t_37))));

			// ================ AGENT 3 AND AGENT 7 END ================ //
			
			// =============== AGENT 4 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_45 = c.int_const("t_45");
		    s.add(t_45 >= (int)segLower + 1 && t_45 <= (int)segUpper);
		    
		    expr t_before_45 = c.int_const("t_before_45");
		    expr t_after_45 = c.int_const("t_after_45");
		    s.add(t_before_45 >= (int)segLower + 1 && t_before_45 <= (int)segUpper && t_after_45 >= (int)segLower && t_after_45 <= (int)segUpper);
		    
		    func_decl rho_45 = function("rho_45", c.int_sort(), c.int_sort());
		    func_decl rho_primed_45 = function("rho_primed_45", c.real_sort(), c.real_sort());
		    
		    func_decl rho_54 = function("rho_54", c.int_sort(), c.int_sort());
		    func_decl rho_primed_54 = function("rho_primed_54", c.real_sort(), c.real_sort());
		    
		    expr pwl_45 = c.int_const("pwl_45");
		    s.add(pwl_45 >= (int)segLower + 1 && pwl_45 <= (int)segUpper);
		    
		    expr pwl_54 = c.int_const("pwl_54");
		    s.add(pwl_54 >= (int)segLower + 1 && pwl_54 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_45(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_45(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_54(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_54(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_45, t_after_45, implies(((t_before_45 < t_after_45) && (t_before_45 >= (int)segLower + 1) && (t_before_45 <= (int)segUpper) && (t_after_45 >= (int)segLower) && (t_after_45 <= (int)segUpper)), ((rho_45(t_before_45) < rho_45(t_after_45)) && (rho_54(t_before_45) < rho_54(t_after_45))))));
			
			//mutual separation constraint
			s.add(forall(pred_4, pred_5, implies(((rho_45(pred_4) == pred_5) && (pred_4 >= (int)segLower + 1) && (pred_4 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_4_x(pred_4)) * (a_5_x(pred_5) - a_4_x(pred_4))) + ((a_5_y(pred_5) - a_4_y(pred_4)) * (a_5_y(pred_5) - a_4_y(pred_4))) + ((a_5_z(pred_5) - a_4_z(pred_4)) * (a_5_z(pred_5) - a_4_z(pred_4))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_45, implies(((pwl_45 >= (int)segLower + 1) && (pwl_45 <= (int)segUpper)), (rho_primed_45(pwl_45) == rho_45(c.int_val(pwl_45)) + ((pwl_45 - c.int_val(pwl_45)) * (rho_45(c.int_val(pwl_45) + 1) - rho_45(c.int_val(pwl_45))))))));
			s.add(forall(pwl_54, implies(((pwl_54 >= (int)segLower + 1) && (pwl_54 <= (int)segUpper)), (rho_primed_54(pwl_54) == rho_54(c.int_val(pwl_54)) + ((pwl_54 - c.int_val(pwl_54)) * (rho_54(c.int_val(pwl_54) + 1) - rho_54(c.int_val(pwl_54))))))));
			
			//inverse re-timing
			s.add(forall(t_45, implies(((t_45 >= (int)segLower) && (t_45 <= (int)segUpper)), (rho_54(rho_45(t_45)) == t_45))));

			// ================ AGENT 4 AND AGENT 5 END ================ //
			
			// =============== AGENT 4 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_46 = c.int_const("t_46");
		    s.add(t_46 >= (int)segLower + 1 && t_46 <= (int)segUpper);
		    
		    expr t_before_46 = c.int_const("t_before_46");
		    expr t_after_46 = c.int_const("t_after_46");
		    s.add(t_before_46 >= (int)segLower + 1 && t_before_46 <= (int)segUpper && t_after_46 >= (int)segLower && t_after_46 <= (int)segUpper);
		    
		    func_decl rho_46 = function("rho_46", c.int_sort(), c.int_sort());
		    func_decl rho_primed_46 = function("rho_primed_46", c.real_sort(), c.real_sort());
		    
		    func_decl rho_64 = function("rho_64", c.int_sort(), c.int_sort());
		    func_decl rho_primed_64 = function("rho_primed_64", c.real_sort(), c.real_sort());
		    
		    expr pwl_46 = c.int_const("pwl_46");
		    s.add(pwl_46 >= (int)segLower + 1 && pwl_46 <= (int)segUpper);
		    
		    expr pwl_64 = c.int_const("pwl_64");
		    s.add(pwl_64 >= (int)segLower + 1 && pwl_64 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_46(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_46(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_64(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_64(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_46, t_after_46, implies(((t_before_46 < t_after_46) && (t_before_46 >= (int)segLower + 1) && (t_before_46 <= (int)segUpper) && (t_after_46 >= (int)segLower) && (t_after_46 <= (int)segUpper)), ((rho_46(t_before_46) < rho_46(t_after_46)) && (rho_64(t_before_46) < rho_64(t_after_46))))));
			
			//mutual separation constraint
			s.add(forall(pred_4, pred_6, implies(((rho_46(pred_4) == pred_6) && (pred_4 >= (int)segLower + 1) && (pred_4 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_4_x(pred_4)) * (a_6_x(pred_6) - a_4_x(pred_4))) + ((a_6_y(pred_6) - a_4_y(pred_4)) * (a_6_y(pred_6) - a_4_y(pred_4))) + ((a_6_z(pred_6) - a_4_z(pred_4)) * (a_6_z(pred_6) - a_4_z(pred_4))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_46, implies(((pwl_46 >= (int)segLower + 1) && (pwl_46 <= (int)segUpper)), (rho_primed_46(pwl_46) == rho_46(c.int_val(pwl_46)) + ((pwl_46 - c.int_val(pwl_46)) * (rho_46(c.int_val(pwl_46) + 1) - rho_46(c.int_val(pwl_46))))))));
			s.add(forall(pwl_64, implies(((pwl_64 >= (int)segLower + 1) && (pwl_64 <= (int)segUpper)), (rho_primed_64(pwl_64) == rho_64(c.int_val(pwl_64)) + ((pwl_64 - c.int_val(pwl_64)) * (rho_64(c.int_val(pwl_64) + 1) - rho_64(c.int_val(pwl_64))))))));
			
			//inverse re-timing
			s.add(forall(t_46, implies(((t_46 >= (int)segLower) && (t_46 <= (int)segUpper)), (rho_64(rho_46(t_46)) == t_46))));

			// ================ AGENT 4 AND AGENT 6 END ================ //
			
			// =============== AGENT 4 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_47 = c.int_const("t_47");
		    s.add(t_47 >= (int)segLower + 1 && t_47 <= (int)segUpper);
		    
		    expr t_before_47 = c.int_const("t_before_47");
		    expr t_after_47 = c.int_const("t_after_47");
		    s.add(t_before_47 >= (int)segLower + 1 && t_before_47 <= (int)segUpper && t_after_47 >= (int)segLower && t_after_47 <= (int)segUpper);
		    
		    func_decl rho_47 = function("rho_47", c.int_sort(), c.int_sort());
		    func_decl rho_primed_47 = function("rho_primed_47", c.real_sort(), c.real_sort());
		    
		    func_decl rho_74 = function("rho_74", c.int_sort(), c.int_sort());
		    func_decl rho_primed_74 = function("rho_primed_74", c.real_sort(), c.real_sort());
		    
		    expr pwl_47 = c.int_const("pwl_47");
		    s.add(pwl_47 >= (int)segLower + 1 && pwl_47 <= (int)segUpper);
		    
		    expr pwl_74 = c.int_const("pwl_74");
		    s.add(pwl_74 >= (int)segLower + 1 && pwl_74 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_47(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_47(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_74(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_74(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_47, t_after_47, implies(((t_before_47 < t_after_47) && (t_before_47 >= (int)segLower + 1) && (t_before_47 <= (int)segUpper) && (t_after_47 >= (int)segLower) && (t_after_47 <= (int)segUpper)), ((rho_47(t_before_47) < rho_47(t_after_47)) && (rho_74(t_before_47) < rho_74(t_after_47))))));
			
			//mutual separation constraint
			s.add(forall(pred_4, pred_7, implies(((rho_47(pred_4) == pred_7) && (pred_4 >= (int)segLower + 1) && (pred_4 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_4_x(pred_4)) * (a_7_x(pred_7) - a_4_x(pred_4))) + ((a_7_y(pred_7) - a_4_y(pred_4)) * (a_7_y(pred_7) - a_4_y(pred_4))) + ((a_7_z(pred_7) - a_4_z(pred_4)) * (a_7_z(pred_7) - a_4_z(pred_4))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_47, implies(((pwl_47 >= (int)segLower + 1) && (pwl_47 <= (int)segUpper)), (rho_primed_47(pwl_47) == rho_47(c.int_val(pwl_47)) + ((pwl_47 - c.int_val(pwl_47)) * (rho_47(c.int_val(pwl_47) + 1) - rho_47(c.int_val(pwl_47))))))));
			s.add(forall(pwl_74, implies(((pwl_74 >= (int)segLower + 1) && (pwl_74 <= (int)segUpper)), (rho_primed_74(pwl_74) == rho_74(c.int_val(pwl_74)) + ((pwl_74 - c.int_val(pwl_74)) * (rho_74(c.int_val(pwl_74) + 1) - rho_74(c.int_val(pwl_74))))))));
			
			//inverse re-timing
			s.add(forall(t_47, implies(((t_47 >= (int)segLower) && (t_47 <= (int)segUpper)), (rho_74(rho_47(t_47)) == t_47))));

			// ================ AGENT 4 AND AGENT 7 END ================ //
			
			// =============== AGENT 5 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_56 = c.int_const("t_56");
		    s.add(t_56 >= (int)segLower + 1 && t_56 <= (int)segUpper);
		    
		    expr t_before_56 = c.int_const("t_before_56");
		    expr t_after_56 = c.int_const("t_after_56");
		    s.add(t_before_56 >= (int)segLower + 1 && t_before_56 <= (int)segUpper && t_after_56 >= (int)segLower && t_after_56 <= (int)segUpper);
		    
		    func_decl rho_56 = function("rho_56", c.int_sort(), c.int_sort());
		    func_decl rho_primed_56 = function("rho_primed_56", c.real_sort(), c.real_sort());
		    
		    func_decl rho_65 = function("rho_65", c.int_sort(), c.int_sort());
		    func_decl rho_primed_65 = function("rho_primed_65", c.real_sort(), c.real_sort());
		    
		    expr pwl_56 = c.int_const("pwl_56");
		    s.add(pwl_56 >= (int)segLower + 1 && pwl_56 <= (int)segUpper);
		    
		    expr pwl_65 = c.int_const("pwl_65");
		    s.add(pwl_65 >= (int)segLower + 1 && pwl_65 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_56(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_56(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_65(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_65(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_56, t_after_56, implies(((t_before_56 < t_after_56) && (t_before_56 >= (int)segLower + 1) && (t_before_56 <= (int)segUpper) && (t_after_56 >= (int)segLower) && (t_after_56 <= (int)segUpper)), ((rho_56(t_before_56) < rho_56(t_after_56)) && (rho_65(t_before_56) < rho_65(t_after_56))))));
			
			//mutual separation constraint
			s.add(forall(pred_5, pred_6, implies(((rho_56(pred_5) == pred_6) && (pred_5 >= (int)segLower + 1) && (pred_5 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_5_x(pred_5)) * (a_6_x(pred_6) - a_5_x(pred_5))) + ((a_6_y(pred_6) - a_5_y(pred_5)) * (a_6_y(pred_6) - a_5_y(pred_5))) + ((a_6_z(pred_6) - a_5_z(pred_5)) * (a_6_z(pred_6) - a_5_z(pred_5))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_56, implies(((pwl_56 >= (int)segLower + 1) && (pwl_56 <= (int)segUpper)), (rho_primed_56(pwl_56) == rho_56(c.int_val(pwl_56)) + ((pwl_56 - c.int_val(pwl_56)) * (rho_56(c.int_val(pwl_56) + 1) - rho_56(c.int_val(pwl_56))))))));
			s.add(forall(pwl_65, implies(((pwl_65 >= (int)segLower + 1) && (pwl_65 <= (int)segUpper)), (rho_primed_65(pwl_65) == rho_65(c.int_val(pwl_65)) + ((pwl_65 - c.int_val(pwl_65)) * (rho_65(c.int_val(pwl_65) + 1) - rho_65(c.int_val(pwl_65))))))));
			
			//inverse re-timing
			s.add(forall(t_56, implies(((t_56 >= (int)segLower) && (t_56 <= (int)segUpper)), (rho_65(rho_56(t_56)) == t_56))));

			// ================ AGENT 5 AND AGENT 6 END ================ //
			
			// =============== AGENT 5 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_57 = c.int_const("t_57");
		    s.add(t_57 >= (int)segLower + 1 && t_57 <= (int)segUpper);
		    
		    expr t_before_57 = c.int_const("t_before_57");
		    expr t_after_57 = c.int_const("t_after_57");
		    s.add(t_before_57 >= (int)segLower + 1 && t_before_57 <= (int)segUpper && t_after_57 >= (int)segLower && t_after_57 <= (int)segUpper);
		    
		    func_decl rho_57 = function("rho_57", c.int_sort(), c.int_sort());
		    func_decl rho_primed_57 = function("rho_primed_57", c.real_sort(), c.real_sort());
		    
		    func_decl rho_75 = function("rho_75", c.int_sort(), c.int_sort());
		    func_decl rho_primed_75 = function("rho_primed_75", c.real_sort(), c.real_sort());
		    
		    expr pwl_57 = c.int_const("pwl_57");
		    s.add(pwl_57 >= (int)segLower + 1 && pwl_57 <= (int)segUpper);
		    
		    expr pwl_75 = c.int_const("pwl_75");
		    s.add(pwl_75 >= (int)segLower + 1 && pwl_75 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_57(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_57(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_75(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_75(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_57, t_after_57, implies(((t_before_57 < t_after_57) && (t_before_57 >= (int)segLower + 1) && (t_before_57 <= (int)segUpper) && (t_after_57 >= (int)segLower) && (t_after_57 <= (int)segUpper)), ((rho_57(t_before_57) < rho_57(t_after_57)) && (rho_75(t_before_57) < rho_75(t_after_57))))));
			
			//mutual separation constraint
			s.add(forall(pred_5, pred_7, implies(((rho_57(pred_5) == pred_7) && (pred_5 >= (int)segLower + 1) && (pred_5 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_5_x(pred_5)) * (a_7_x(pred_7) - a_5_x(pred_5))) + ((a_7_y(pred_7) - a_5_y(pred_5)) * (a_7_y(pred_7) - a_5_y(pred_5))) + ((a_7_z(pred_7) - a_5_z(pred_5)) * (a_7_z(pred_7) - a_5_z(pred_5))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_57, implies(((pwl_57 >= (int)segLower + 1) && (pwl_57 <= (int)segUpper)), (rho_primed_57(pwl_57) == rho_57(c.int_val(pwl_57)) + ((pwl_57 - c.int_val(pwl_57)) * (rho_57(c.int_val(pwl_57) + 1) - rho_57(c.int_val(pwl_57))))))));
			s.add(forall(pwl_75, implies(((pwl_75 >= (int)segLower + 1) && (pwl_75 <= (int)segUpper)), (rho_primed_75(pwl_75) == rho_75(c.int_val(pwl_75)) + ((pwl_75 - c.int_val(pwl_75)) * (rho_75(c.int_val(pwl_75) + 1) - rho_75(c.int_val(pwl_75))))))));
			
			//inverse re-timing
			s.add(forall(t_57, implies(((t_57 >= (int)segLower) && (t_57 <= (int)segUpper)), (rho_75(rho_57(t_57)) == t_57))));

			// ================ AGENT 5 AND AGENT 7 END ================ //
			
			// =============== AGENT 6 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_67 = c.int_const("t_67");
		    s.add(t_67 >= (int)segLower + 1 && t_67 <= (int)segUpper);
		    
		    expr t_before_67 = c.int_const("t_before_67");
		    expr t_after_67 = c.int_const("t_after_67");
		    s.add(t_before_67 >= (int)segLower + 1 && t_before_67 <= (int)segUpper && t_after_67 >= (int)segLower && t_after_67 <= (int)segUpper);
		    
		    func_decl rho_67 = function("rho_67", c.int_sort(), c.int_sort());
		    func_decl rho_primed_67 = function("rho_primed_67", c.real_sort(), c.real_sort());
		    
		    func_decl rho_76 = function("rho_76", c.int_sort(), c.int_sort());
		    func_decl rho_primed_76 = function("rho_primed_76", c.real_sort(), c.real_sort());
		    
		    expr pwl_67 = c.int_const("pwl_67");
		    s.add(pwl_67 >= (int)segLower + 1 && pwl_67 <= (int)segUpper);
		    
		    expr pwl_76 = c.int_const("pwl_76");
		    s.add(pwl_76 >= (int)segLower + 1 && pwl_76 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_67(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_67(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_76(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_76(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_67, t_after_67, implies(((t_before_67 < t_after_67) && (t_before_67 >= (int)segLower + 1) && (t_before_67 <= (int)segUpper) && (t_after_67 >= (int)segLower) && (t_after_67 <= (int)segUpper)), ((rho_67(t_before_67) < rho_67(t_after_67)) && (rho_76(t_before_67) < rho_76(t_after_67))))));
			
			//mutual separation constraint
			s.add(forall(pred_6, pred_7, implies(((rho_67(pred_6) == pred_7) && (pred_6 >= (int)segLower + 1) && (pred_6 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_6_x(pred_6)) * (a_7_x(pred_7) - a_6_x(pred_6))) + ((a_7_y(pred_7) - a_6_y(pred_6)) * (a_7_y(pred_7) - a_6_y(pred_6))) + ((a_7_z(pred_7) - a_6_z(pred_6)) * (a_7_z(pred_7) - a_6_z(pred_6))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_67, implies(((pwl_67 >= (int)segLower + 1) && (pwl_67 <= (int)segUpper)), (rho_primed_67(pwl_67) == rho_67(c.int_val(pwl_67)) + ((pwl_67 - c.int_val(pwl_67)) * (rho_67(c.int_val(pwl_67) + 1) - rho_67(c.int_val(pwl_67))))))));
			s.add(forall(pwl_76, implies(((pwl_76 >= (int)segLower + 1) && (pwl_76 <= (int)segUpper)), (rho_primed_76(pwl_76) == rho_76(c.int_val(pwl_76)) + ((pwl_76 - c.int_val(pwl_76)) * (rho_76(c.int_val(pwl_76) + 1) - rho_76(c.int_val(pwl_76))))))));
			
			//inverse re-timing
			s.add(forall(t_67, implies(((t_67 >= (int)segLower) && (t_67 <= (int)segUpper)), (rho_76(rho_67(t_67)) == t_67))));

			// ================ AGENT 6 AND AGENT 7 END ================ //
			
			if(s.check() == sat)
		    {
		    	std::string verdict = std::to_string(i) + " : Sat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    else
		    {
		    	std::string verdict = std::to_string(i) + " : Unsat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    
		    //reset solver
		    //s.reset();
		    
		    //build and show model
		    //model m = s.get_model();
    		//std::cout << m << "\n";
	    }
	}
	//return verdicts;
}

void runSolver_9(double eps, int segCount, double sigDur, int msgLim)
{
	//enable parallel mode
	//set_param("parallel.enable", true);
	
	//get data
	std::vector<std::vector<std::string>> agentData_0 = getData("agent_0.txt");
	std::vector<std::vector<std::string>> agentData_1 = getData("agent_1.txt");
	std::vector<std::vector<std::string>> agentData_2 = getData("agent_2.txt");
	std::vector<std::vector<std::string>> agentData_3 = getData("agent_3.txt");
	std::vector<std::vector<std::string>> agentData_4 = getData("agent_4.txt");
	std::vector<std::vector<std::string>> agentData_5 = getData("agent_5.txt");
	std::vector<std::vector<std::string>> agentData_6 = getData("agent_6.txt");
	std::vector<std::vector<std::string>> agentData_7 = getData("agent_7.txt");
	std::vector<std::vector<std::string>> agentData_8 = getData("agent_8.txt");
	
	//safety checks
	if(!(std::stod(agentData_0[0][0]) == 0 && std::stod(agentData_1[0][0]) == 0))
	{
		return;
	}
	
	if(std::stod(agentData_0[1][0]) != std::stod(agentData_1[1][0]))
	{
		return;
	}
	
	//second time-stamp on agent that is to be re-timed
	double t1 = std::stod(agentData_0[1][0]);
	
	//delta
	int delta = 0;
	
	//segment duration
	double segDur = sigDur / segCount;
	
	//check if the segment duration is smaller than the sampling period
	if(segDur < t1)
	{
		segCount = sigDur / t1;
	}
	
	//multiplier for normalization
	double mult = 1 / t1;
	
	//normalization of paramters
	eps *= mult;
	sigDur *= mult;
	segDur *= mult;
	
	//verdict vector
	std::vector<std::string> verdicts;
	
	#pragma omp parallel
	{
		#pragma omp for
		for(int i = 0; i < segCount; i++) 
	    {			
			//segment bounds
			double segLower = (i * segDur) - eps;
			double segUpper = (i + 1) * segDur;
			
		    context c;

		    //solver
		    solver s(c);
		    
		    //co-ord functions
		    func_decl a_0_x = function("a_0_x", c.int_sort(), c.real_sort());
		    func_decl a_0_y = function("a_0_y", c.int_sort(), c.real_sort());
		    func_decl a_0_z = function("a_0_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_1_x = function("a_1_x", c.int_sort(), c.real_sort());
		    func_decl a_1_y = function("a_1_y", c.int_sort(), c.real_sort());
		    func_decl a_1_z = function("a_1_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_2_x = function("a_2_x", c.int_sort(), c.real_sort());
		    func_decl a_2_y = function("a_2_y", c.int_sort(), c.real_sort());
		    func_decl a_2_z = function("a_2_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_3_x = function("a_3_x", c.int_sort(), c.real_sort());
		    func_decl a_3_y = function("a_3_y", c.int_sort(), c.real_sort());
		    func_decl a_3_z = function("a_3_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_4_x = function("a_4_x", c.int_sort(), c.real_sort());
		    func_decl a_4_y = function("a_4_y", c.int_sort(), c.real_sort());
		    func_decl a_4_z = function("a_4_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_5_x = function("a_5_x", c.int_sort(), c.real_sort());
		    func_decl a_5_y = function("a_5_y", c.int_sort(), c.real_sort());
		    func_decl a_5_z = function("a_5_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_6_x = function("a_6_x", c.int_sort(), c.real_sort());
		    func_decl a_6_y = function("a_6_y", c.int_sort(), c.real_sort());
		    func_decl a_6_z = function("a_6_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_7_x = function("a_7_x", c.int_sort(), c.real_sort());
		    func_decl a_7_y = function("a_7_y", c.int_sort(), c.real_sort());
		    func_decl a_7_z = function("a_7_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_8_x = function("a_8_x", c.int_sort(), c.real_sort());
		    func_decl a_8_y = function("a_8_y", c.int_sort(), c.real_sort());
		    func_decl a_8_z = function("a_8_z", c.int_sort(), c.real_sort());
		    
		    //populate co-ord functions
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_0.size())
		        {
		        	s.add(a_0_x(j) == c.real_val(agentData_0[j][1].c_str()));
		        	s.add(a_0_y(j) == c.real_val(agentData_0[j][2].c_str()));
		        	s.add(a_0_z(j) == c.real_val(agentData_0[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_1.size())
		        {
		        	s.add(a_1_x(j) == c.real_val(agentData_1[j][1].c_str()));
		        	s.add(a_1_y(j) == c.real_val(agentData_1[j][2].c_str()));
		        	s.add(a_1_z(j) == c.real_val(agentData_1[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_2.size())
		        {
		        	s.add(a_2_x(j) == c.real_val(agentData_2[j][1].c_str()));
		        	s.add(a_2_y(j) == c.real_val(agentData_2[j][2].c_str()));
		        	s.add(a_2_z(j) == c.real_val(agentData_2[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_3.size())
		        {
		        	s.add(a_3_x(j) == c.real_val(agentData_3[j][1].c_str()));
		        	s.add(a_3_y(j) == c.real_val(agentData_3[j][2].c_str()));
		        	s.add(a_3_z(j) == c.real_val(agentData_3[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_4.size())
		        {
		        	s.add(a_4_x(j) == c.real_val(agentData_4[j][1].c_str()));
		        	s.add(a_4_y(j) == c.real_val(agentData_4[j][2].c_str()));
		        	s.add(a_4_z(j) == c.real_val(agentData_4[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_5.size())
		        {
		        	s.add(a_5_x(j) == c.real_val(agentData_5[j][1].c_str()));
		        	s.add(a_5_y(j) == c.real_val(agentData_5[j][2].c_str()));
		        	s.add(a_5_z(j) == c.real_val(agentData_5[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_6.size())
		        {
		        	s.add(a_6_x(j) == c.real_val(agentData_6[j][1].c_str()));
		        	s.add(a_6_y(j) == c.real_val(agentData_6[j][2].c_str()));
		        	s.add(a_6_z(j) == c.real_val(agentData_6[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_7.size())
		        {
		        	s.add(a_7_x(j) == c.real_val(agentData_7[j][1].c_str()));
		        	s.add(a_7_y(j) == c.real_val(agentData_7[j][2].c_str()));
		        	s.add(a_7_z(j) == c.real_val(agentData_7[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_8.size())
		        {
		        	s.add(a_8_x(j) == c.real_val(agentData_8[j][1].c_str()));
		        	s.add(a_8_y(j) == c.real_val(agentData_8[j][2].c_str()));
		        	s.add(a_8_z(j) == c.real_val(agentData_8[j][3].c_str()));
				}
		    }
		    
		    //general smt variables		  
			expr pred_0 = c.int_const("pred_0");
			s.add(pred_0 >= (int)segLower + 1 && pred_0 <= (int)segUpper);
			
		    expr pred_1 = c.int_const("pred_1");
		    s.add(pred_1 >= (int)segLower + 1 && pred_1 <= (int)segUpper);
		    
		    expr pred_2 = c.int_const("pred_2");
		    s.add(pred_2 >= (int)segLower + 1 && pred_2 <= (int)segUpper);
		    
		    expr pred_3 = c.int_const("pred_3");
		    s.add(pred_3 >= (int)segLower + 1 && pred_3 <= (int)segUpper);
		    
		    expr pred_4 = c.int_const("pred_4");
		    s.add(pred_4 >= (int)segLower + 1 && pred_4 <= (int)segUpper);
		    
		    expr pred_5 = c.int_const("pred_5");
		    s.add(pred_5 >= (int)segLower + 1 && pred_5 <= (int)segUpper);
		    
		    expr pred_6 = c.int_const("pred_6");
		    s.add(pred_6 >= (int)segLower + 1 && pred_6 <= (int)segUpper);
		    
		    expr pred_7 = c.int_const("pred_7");
		    s.add(pred_7 >= (int)segLower + 1 && pred_7 <= (int)segUpper);
		    
		    expr pred_8 = c.int_const("pred_8");
		    s.add(pred_8 >= (int)segLower + 1 && pred_8 <= (int)segUpper);
		    
		    // =============== AGENT 0 AND AGENT 1 START =============== //
			
			//agent pair smt variables
			expr t_01 = c.int_const("t_01");
		    s.add(t_01 >= (int)segLower + 1 && t_01 <= (int)segUpper);
		    
		    expr t_before_01 = c.int_const("t_before_01");
		    expr t_after_01 = c.int_const("t_after_01");
		    s.add(t_before_01 >= (int)segLower + 1 && t_before_01 <= (int)segUpper && t_after_01 >= (int)segLower && t_after_01 <= (int)segUpper);
		    
		    func_decl rho_01 = function("rho_01", c.int_sort(), c.int_sort());
		    func_decl rho_primed_01 = function("rho_primed_01", c.real_sort(), c.real_sort());
		    
		    func_decl rho_10 = function("rho_10", c.int_sort(), c.int_sort());
		    func_decl rho_primed_10 = function("rho_primed_10", c.real_sort(), c.real_sort());
		    
		    expr pwl_01 = c.int_const("pwl_01");
		    s.add(pwl_01 >= (int)segLower + 1 && pwl_01 <= (int)segUpper);
		    
		    expr pwl_10 = c.int_const("pwl_10");
		    s.add(pwl_10 >= (int)segLower + 1 && pwl_10 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_01, t_after_01, implies(((t_before_01 < t_after_01) && (t_before_01 >= (int)segLower + 1) && (t_before_01 <= (int)segUpper) && (t_after_01 >= (int)segLower) && (t_after_01 <= (int)segUpper)), ((rho_01(t_before_01) < rho_01(t_after_01)) && (rho_10(t_before_01) < rho_10(t_after_01))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_1, implies(((rho_01(pred_0) == pred_1) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_1 >= (int)segLower) && (pred_1 <= (int)segUpper)), (c.real_val(delta) <= (((a_1_x(pred_1) - a_0_x(pred_0)) * (a_1_x(pred_1) - a_0_x(pred_0))) + ((a_1_y(pred_1) - a_0_y(pred_0)) * (a_1_y(pred_1) - a_0_y(pred_0))) + ((a_1_z(pred_1) - a_0_z(pred_0)) * (a_1_z(pred_1) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_01, implies(((pwl_01 >= (int)segLower + 1) && (pwl_01 <= (int)segUpper)), (rho_primed_01(pwl_01) == rho_01(c.int_val(pwl_01)) + ((pwl_01 - c.int_val(pwl_01)) * (rho_01(c.int_val(pwl_01) + 1) - rho_01(c.int_val(pwl_01))))))));
			s.add(forall(pwl_10, implies(((pwl_10 >= (int)segLower + 1) && (pwl_10 <= (int)segUpper)), (rho_primed_10(pwl_10) == rho_10(c.int_val(pwl_10)) + ((pwl_10 - c.int_val(pwl_10)) * (rho_10(c.int_val(pwl_10) + 1) - rho_10(c.int_val(pwl_10))))))));
			
			//inverse re-timing
			s.add(forall(t_01, implies(((t_01 >= (int)segLower) && (t_01 <= (int)segUpper)), (rho_10(rho_01(t_01)) == t_01))));

			// ================ AGENT 0 AND AGENT 1 END ================ //
			
			// =============== AGENT 0 AND AGENT 2 START =============== //
			
			//agent pair smt variables
			expr t_02 = c.int_const("t_02");
		    s.add(t_02 >= (int)segLower + 1 && t_02 <= (int)segUpper);
		    
		    expr t_before_02 = c.int_const("t_before_02");
		    expr t_after_02 = c.int_const("t_after_02");
		    s.add(t_before_02 >= (int)segLower + 1 && t_before_02 <= (int)segUpper && t_after_02 >= (int)segLower && t_after_02 <= (int)segUpper);
		    
		    func_decl rho_02 = function("rho_02", c.int_sort(), c.int_sort());
		    func_decl rho_primed_02 = function("rho_primed_02", c.real_sort(), c.real_sort());
		    
		    func_decl rho_20 = function("rho_20", c.int_sort(), c.int_sort());
		    func_decl rho_primed_20 = function("rho_primed_20", c.real_sort(), c.real_sort());
		    
		    expr pwl_02 = c.int_const("pwl_02");
		    s.add(pwl_02 >= (int)segLower + 1 && pwl_02 <= (int)segUpper);
		    
		    expr pwl_20 = c.int_const("pwl_20");
		    s.add(pwl_20 >= (int)segLower + 1 && pwl_20 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_02(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_02(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_20(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_20(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_02, t_after_02, implies(((t_before_02 < t_after_02) && (t_before_02 >= (int)segLower + 1) && (t_before_02 <= (int)segUpper) && (t_after_02 >= (int)segLower) && (t_after_02 <= (int)segUpper)), ((rho_02(t_before_02) < rho_02(t_after_02)) && (rho_20(t_before_02) < rho_20(t_after_02))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_2, implies(((rho_02(pred_0) == pred_2) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_2 >= (int)segLower) && (pred_2 <= (int)segUpper)), (c.real_val(delta) <= (((a_2_x(pred_2) - a_0_x(pred_0)) * (a_2_x(pred_2) - a_0_x(pred_0))) + ((a_2_y(pred_2) - a_0_y(pred_0)) * (a_2_y(pred_2) - a_0_y(pred_0))) + ((a_2_z(pred_2) - a_0_z(pred_0)) * (a_2_z(pred_2) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_02, implies(((pwl_02 >= (int)segLower + 1) && (pwl_02 <= (int)segUpper)), (rho_primed_02(pwl_02) == rho_02(c.int_val(pwl_02)) + ((pwl_02 - c.int_val(pwl_02)) * (rho_02(c.int_val(pwl_02) + 1) - rho_02(c.int_val(pwl_02))))))));
			s.add(forall(pwl_20, implies(((pwl_20 >= (int)segLower + 1) && (pwl_20 <= (int)segUpper)), (rho_primed_20(pwl_20) == rho_20(c.int_val(pwl_20)) + ((pwl_20 - c.int_val(pwl_20)) * (rho_20(c.int_val(pwl_20) + 1) - rho_20(c.int_val(pwl_20))))))));
			
			//inverse re-timing
			s.add(forall(t_02, implies(((t_02 >= (int)segLower) && (t_02 <= (int)segUpper)), (rho_20(rho_02(t_02)) == t_02))));

			// ================ AGENT 0 AND AGENT 2 END ================ //
			
			// =============== AGENT 0 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_03 = c.int_const("t_03");
		    s.add(t_03 >= (int)segLower + 1 && t_03 <= (int)segUpper);
		    
		    expr t_before_03 = c.int_const("t_before_03");
		    expr t_after_03 = c.int_const("t_after_03");
		    s.add(t_before_03 >= (int)segLower + 1 && t_before_03 <= (int)segUpper && t_after_03 >= (int)segLower && t_after_03 <= (int)segUpper);
		    
		    func_decl rho_03 = function("rho_03", c.int_sort(), c.int_sort());
		    func_decl rho_primed_03 = function("rho_primed_03", c.real_sort(), c.real_sort());
		    
		    func_decl rho_30 = function("rho_30", c.int_sort(), c.int_sort());
		    func_decl rho_primed_30 = function("rho_primed_30", c.real_sort(), c.real_sort());
		    
		    expr pwl_03 = c.int_const("pwl_03");
		    s.add(pwl_03 >= (int)segLower + 1 && pwl_03 <= (int)segUpper);
		    
		    expr pwl_30 = c.int_const("pwl_30");
		    s.add(pwl_30 >= (int)segLower + 1 && pwl_30 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_03(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_03(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_30(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_30(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_03, t_after_03, implies(((t_before_03 < t_after_03) && (t_before_03 >= (int)segLower + 1) && (t_before_03 <= (int)segUpper) && (t_after_03 >= (int)segLower) && (t_after_03 <= (int)segUpper)), ((rho_03(t_before_03) < rho_03(t_after_03)) && (rho_30(t_before_03) < rho_30(t_after_03))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_3, implies(((rho_03(pred_0) == pred_3) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_0_x(pred_0)) * (a_3_x(pred_3) - a_0_x(pred_0))) + ((a_3_y(pred_3) - a_0_y(pred_0)) * (a_3_y(pred_3) - a_0_y(pred_0))) + ((a_3_z(pred_3) - a_0_z(pred_0)) * (a_3_z(pred_3) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_03, implies(((pwl_03 >= (int)segLower + 1) && (pwl_03 <= (int)segUpper)), (rho_primed_03(pwl_03) == rho_03(c.int_val(pwl_03)) + ((pwl_03 - c.int_val(pwl_03)) * (rho_03(c.int_val(pwl_03) + 1) - rho_03(c.int_val(pwl_03))))))));
			s.add(forall(pwl_30, implies(((pwl_30 >= (int)segLower + 1) && (pwl_30 <= (int)segUpper)), (rho_primed_30(pwl_30) == rho_30(c.int_val(pwl_30)) + ((pwl_30 - c.int_val(pwl_30)) * (rho_30(c.int_val(pwl_30) + 1) - rho_30(c.int_val(pwl_30))))))));
			
			//inverse re-timing
			s.add(forall(t_03, implies(((t_03 >= (int)segLower) && (t_03 <= (int)segUpper)), (rho_30(rho_03(t_03)) == t_03))));

			// ================ AGENT 0 AND AGENT 3 END ================ //
			
			// =============== AGENT 0 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_04 = c.int_const("t_04");
		    s.add(t_04 >= (int)segLower + 1 && t_04 <= (int)segUpper);
		    
		    expr t_before_04 = c.int_const("t_before_04");
		    expr t_after_04 = c.int_const("t_after_04");
		    s.add(t_before_04 >= (int)segLower + 1 && t_before_04 <= (int)segUpper && t_after_04 >= (int)segLower && t_after_04 <= (int)segUpper);
		    
		    func_decl rho_04 = function("rho_04", c.int_sort(), c.int_sort());
		    func_decl rho_primed_04 = function("rho_primed_04", c.real_sort(), c.real_sort());
		    
		    func_decl rho_40 = function("rho_40", c.int_sort(), c.int_sort());
		    func_decl rho_primed_40 = function("rho_primed_40", c.real_sort(), c.real_sort());
		    
		    expr pwl_04 = c.int_const("pwl_04");
		    s.add(pwl_04 >= (int)segLower + 1 && pwl_04 <= (int)segUpper);
		    
		    expr pwl_40 = c.int_const("pwl_40");
		    s.add(pwl_40 >= (int)segLower + 1 && pwl_40 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_04(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_04(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_40(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_40(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_04, t_after_04, implies(((t_before_04 < t_after_04) && (t_before_04 >= (int)segLower + 1) && (t_before_04 <= (int)segUpper) && (t_after_04 >= (int)segLower) && (t_after_04 <= (int)segUpper)), ((rho_04(t_before_04) < rho_04(t_after_04)) && (rho_40(t_before_04) < rho_40(t_after_04))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_4, implies(((rho_04(pred_0) == pred_4) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_0_x(pred_0)) * (a_4_x(pred_4) - a_0_x(pred_0))) + ((a_4_y(pred_4) - a_0_y(pred_0)) * (a_4_y(pred_4) - a_0_y(pred_0))) + ((a_4_z(pred_4) - a_0_z(pred_0)) * (a_4_z(pred_4) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_04, implies(((pwl_04 >= (int)segLower + 1) && (pwl_04 <= (int)segUpper)), (rho_primed_04(pwl_04) == rho_04(c.int_val(pwl_04)) + ((pwl_04 - c.int_val(pwl_04)) * (rho_04(c.int_val(pwl_04) + 1) - rho_04(c.int_val(pwl_04))))))));
			s.add(forall(pwl_40, implies(((pwl_40 >= (int)segLower + 1) && (pwl_40 <= (int)segUpper)), (rho_primed_40(pwl_40) == rho_40(c.int_val(pwl_40)) + ((pwl_40 - c.int_val(pwl_40)) * (rho_40(c.int_val(pwl_40) + 1) - rho_40(c.int_val(pwl_40))))))));
			
			//inverse re-timing
			s.add(forall(t_04, implies(((t_04 >= (int)segLower) && (t_04 <= (int)segUpper)), (rho_40(rho_04(t_04)) == t_04))));

			// ================ AGENT 0 AND AGENT 4 END ================ //
			
			// =============== AGENT 0 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_05 = c.int_const("t_05");
		    s.add(t_05 >= (int)segLower + 1 && t_05 <= (int)segUpper);
		    
		    expr t_before_05 = c.int_const("t_before_05");
		    expr t_after_05 = c.int_const("t_after_05");
		    s.add(t_before_05 >= (int)segLower + 1 && t_before_05 <= (int)segUpper && t_after_05 >= (int)segLower && t_after_05 <= (int)segUpper);
		    
		    func_decl rho_05 = function("rho_05", c.int_sort(), c.int_sort());
		    func_decl rho_primed_05 = function("rho_primed_05", c.real_sort(), c.real_sort());
		    
		    func_decl rho_50 = function("rho_50", c.int_sort(), c.int_sort());
		    func_decl rho_primed_50 = function("rho_primed_50", c.real_sort(), c.real_sort());
		    
		    expr pwl_05 = c.int_const("pwl_05");
		    s.add(pwl_05 >= (int)segLower + 1 && pwl_05 <= (int)segUpper);
		    
		    expr pwl_50 = c.int_const("pwl_50");
		    s.add(pwl_50 >= (int)segLower + 1 && pwl_50 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_05(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_05(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_50(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_50(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_05, t_after_05, implies(((t_before_05 < t_after_05) && (t_before_05 >= (int)segLower + 1) && (t_before_05 <= (int)segUpper) && (t_after_05 >= (int)segLower) && (t_after_05 <= (int)segUpper)), ((rho_05(t_before_05) < rho_05(t_after_05)) && (rho_50(t_before_05) < rho_50(t_after_05))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_5, implies(((rho_05(pred_0) == pred_5) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_0_x(pred_0)) * (a_5_x(pred_5) - a_0_x(pred_0))) + ((a_5_y(pred_5) - a_0_y(pred_0)) * (a_5_y(pred_5) - a_0_y(pred_0))) + ((a_5_z(pred_5) - a_0_z(pred_0)) * (a_5_z(pred_5) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_05, implies(((pwl_05 >= (int)segLower + 1) && (pwl_05 <= (int)segUpper)), (rho_primed_05(pwl_05) == rho_05(c.int_val(pwl_05)) + ((pwl_05 - c.int_val(pwl_05)) * (rho_05(c.int_val(pwl_05) + 1) - rho_05(c.int_val(pwl_05))))))));
			s.add(forall(pwl_50, implies(((pwl_50 >= (int)segLower + 1) && (pwl_50 <= (int)segUpper)), (rho_primed_50(pwl_50) == rho_50(c.int_val(pwl_50)) + ((pwl_50 - c.int_val(pwl_50)) * (rho_50(c.int_val(pwl_50) + 1) - rho_50(c.int_val(pwl_50))))))));
			
			//inverse re-timing
			s.add(forall(t_05, implies(((t_05 >= (int)segLower) && (t_05 <= (int)segUpper)), (rho_50(rho_05(t_05)) == t_05))));

			// ================ AGENT 0 AND AGENT 5 END ================ //
			
			// =============== AGENT 0 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_06 = c.int_const("t_06");
		    s.add(t_06 >= (int)segLower + 1 && t_06 <= (int)segUpper);
		    
		    expr t_before_06 = c.int_const("t_before_06");
		    expr t_after_06 = c.int_const("t_after_06");
		    s.add(t_before_06 >= (int)segLower + 1 && t_before_06 <= (int)segUpper && t_after_06 >= (int)segLower && t_after_06 <= (int)segUpper);
		    
		    func_decl rho_06 = function("rho_06", c.int_sort(), c.int_sort());
		    func_decl rho_primed_06 = function("rho_primed_06", c.real_sort(), c.real_sort());
		    
		    func_decl rho_60 = function("rho_60", c.int_sort(), c.int_sort());
		    func_decl rho_primed_60 = function("rho_primed_60", c.real_sort(), c.real_sort());
		    
		    expr pwl_06 = c.int_const("pwl_06");
		    s.add(pwl_06 >= (int)segLower + 1 && pwl_06 <= (int)segUpper);
		    
		    expr pwl_60 = c.int_const("pwl_60");
		    s.add(pwl_60 >= (int)segLower + 1 && pwl_60 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_06(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_06(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_60(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_60(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_06, t_after_06, implies(((t_before_06 < t_after_06) && (t_before_06 >= (int)segLower + 1) && (t_before_06 <= (int)segUpper) && (t_after_06 >= (int)segLower) && (t_after_06 <= (int)segUpper)), ((rho_06(t_before_06) < rho_06(t_after_06)) && (rho_60(t_before_06) < rho_60(t_after_06))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_6, implies(((rho_06(pred_0) == pred_6) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_0_x(pred_0)) * (a_6_x(pred_6) - a_0_x(pred_0))) + ((a_6_y(pred_6) - a_0_y(pred_0)) * (a_6_y(pred_6) - a_0_y(pred_0))) + ((a_6_z(pred_6) - a_0_z(pred_0)) * (a_6_z(pred_6) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_06, implies(((pwl_06 >= (int)segLower + 1) && (pwl_06 <= (int)segUpper)), (rho_primed_06(pwl_06) == rho_06(c.int_val(pwl_06)) + ((pwl_06 - c.int_val(pwl_06)) * (rho_06(c.int_val(pwl_06) + 1) - rho_06(c.int_val(pwl_06))))))));
			s.add(forall(pwl_60, implies(((pwl_60 >= (int)segLower + 1) && (pwl_60 <= (int)segUpper)), (rho_primed_60(pwl_60) == rho_60(c.int_val(pwl_60)) + ((pwl_60 - c.int_val(pwl_60)) * (rho_60(c.int_val(pwl_60) + 1) - rho_60(c.int_val(pwl_60))))))));
			
			//inverse re-timing
			s.add(forall(t_06, implies(((t_06 >= (int)segLower) && (t_06 <= (int)segUpper)), (rho_60(rho_06(t_06)) == t_06))));

			// ================ AGENT 0 AND AGENT 6 END ================ //
			
			// =============== AGENT 0 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_07 = c.int_const("t_07");
		    s.add(t_07 >= (int)segLower + 1 && t_07 <= (int)segUpper);
		    
		    expr t_before_07 = c.int_const("t_before_07");
		    expr t_after_07 = c.int_const("t_after_07");
		    s.add(t_before_07 >= (int)segLower + 1 && t_before_07 <= (int)segUpper && t_after_07 >= (int)segLower && t_after_07 <= (int)segUpper);
		    
		    func_decl rho_07 = function("rho_07", c.int_sort(), c.int_sort());
		    func_decl rho_primed_07 = function("rho_primed_07", c.real_sort(), c.real_sort());
		    
		    func_decl rho_70 = function("rho_70", c.int_sort(), c.int_sort());
		    func_decl rho_primed_70 = function("rho_primed_70", c.real_sort(), c.real_sort());
		    
		    expr pwl_07 = c.int_const("pwl_07");
		    s.add(pwl_07 >= (int)segLower + 1 && pwl_07 <= (int)segUpper);
		    
		    expr pwl_70 = c.int_const("pwl_70");
		    s.add(pwl_70 >= (int)segLower + 1 && pwl_70 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_07(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_07(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_70(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_70(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_07, t_after_07, implies(((t_before_07 < t_after_07) && (t_before_07 >= (int)segLower + 1) && (t_before_07 <= (int)segUpper) && (t_after_07 >= (int)segLower) && (t_after_07 <= (int)segUpper)), ((rho_07(t_before_07) < rho_07(t_after_07)) && (rho_70(t_before_07) < rho_70(t_after_07))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_7, implies(((rho_07(pred_0) == pred_7) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_0_x(pred_0)) * (a_7_x(pred_7) - a_0_x(pred_0))) + ((a_7_y(pred_7) - a_0_y(pred_0)) * (a_7_y(pred_7) - a_0_y(pred_0))) + ((a_7_z(pred_7) - a_0_z(pred_0)) * (a_7_z(pred_7) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_07, implies(((pwl_07 >= (int)segLower + 1) && (pwl_07 <= (int)segUpper)), (rho_primed_07(pwl_07) == rho_07(c.int_val(pwl_07)) + ((pwl_07 - c.int_val(pwl_07)) * (rho_07(c.int_val(pwl_07) + 1) - rho_07(c.int_val(pwl_07))))))));
			s.add(forall(pwl_70, implies(((pwl_70 >= (int)segLower + 1) && (pwl_70 <= (int)segUpper)), (rho_primed_70(pwl_70) == rho_70(c.int_val(pwl_70)) + ((pwl_70 - c.int_val(pwl_70)) * (rho_70(c.int_val(pwl_70) + 1) - rho_70(c.int_val(pwl_70))))))));
			
			//inverse re-timing
			s.add(forall(t_07, implies(((t_07 >= (int)segLower) && (t_07 <= (int)segUpper)), (rho_70(rho_07(t_07)) == t_07))));

			// ================ AGENT 0 AND AGENT 7 END ================ //
			
			// =============== AGENT 0 AND AGENT 8 START =============== //
			
			//agent pair smt variables
			expr t_08 = c.int_const("t_08");
		    s.add(t_08 >= (int)segLower + 1 && t_08 <= (int)segUpper);
		    
		    expr t_before_08 = c.int_const("t_before_08");
		    expr t_after_08 = c.int_const("t_after_08");
		    s.add(t_before_08 >= (int)segLower + 1 && t_before_08 <= (int)segUpper && t_after_08 >= (int)segLower && t_after_08 <= (int)segUpper);
		    
		    func_decl rho_08 = function("rho_08", c.int_sort(), c.int_sort());
		    func_decl rho_primed_08 = function("rho_primed_08", c.real_sort(), c.real_sort());
		    
		    func_decl rho_80 = function("rho_80", c.int_sort(), c.int_sort());
		    func_decl rho_primed_80 = function("rho_primed_80", c.real_sort(), c.real_sort());
		    
		    expr pwl_08 = c.int_const("pwl_08");
		    s.add(pwl_08 >= (int)segLower + 1 && pwl_08 <= (int)segUpper);
		    
		    expr pwl_80 = c.int_const("pwl_80");
		    s.add(pwl_80 >= (int)segLower + 1 && pwl_80 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_08(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_08(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_80(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_80(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_08, t_after_08, implies(((t_before_08 < t_after_08) && (t_before_08 >= (int)segLower + 1) && (t_before_08 <= (int)segUpper) && (t_after_08 >= (int)segLower) && (t_after_08 <= (int)segUpper)), ((rho_08(t_before_08) < rho_08(t_after_08)) && (rho_80(t_before_08) < rho_80(t_after_08))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_8, implies(((rho_08(pred_0) == pred_8) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_8 >= (int)segLower) && (pred_8 <= (int)segUpper)), (c.real_val(delta) <= (((a_8_x(pred_8) - a_0_x(pred_0)) * (a_8_x(pred_8) - a_0_x(pred_0))) + ((a_8_y(pred_8) - a_0_y(pred_0)) * (a_8_y(pred_8) - a_0_y(pred_0))) + ((a_8_z(pred_8) - a_0_z(pred_0)) * (a_8_z(pred_8) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_08, implies(((pwl_08 >= (int)segLower + 1) && (pwl_08 <= (int)segUpper)), (rho_primed_08(pwl_08) == rho_08(c.int_val(pwl_08)) + ((pwl_08 - c.int_val(pwl_08)) * (rho_08(c.int_val(pwl_08) + 1) - rho_08(c.int_val(pwl_08))))))));
			s.add(forall(pwl_80, implies(((pwl_80 >= (int)segLower + 1) && (pwl_80 <= (int)segUpper)), (rho_primed_80(pwl_80) == rho_80(c.int_val(pwl_80)) + ((pwl_80 - c.int_val(pwl_80)) * (rho_80(c.int_val(pwl_80) + 1) - rho_80(c.int_val(pwl_80))))))));
			
			//inverse re-timing
			s.add(forall(t_08, implies(((t_08 >= (int)segLower) && (t_08 <= (int)segUpper)), (rho_80(rho_08(t_08)) == t_08))));

			// ================ AGENT 0 AND AGENT 8 END ================ //
			
			// =============== AGENT 1 AND AGENT 2 START =============== //
			
			//agent pair smt variables
			expr t_12 = c.int_const("t_12");
		    s.add(t_12 >= (int)segLower + 1 && t_12 <= (int)segUpper);
		    
		    expr t_before_12 = c.int_const("t_before_12");
		    expr t_after_12 = c.int_const("t_after_12");
		    s.add(t_before_12 >= (int)segLower + 1 && t_before_12 <= (int)segUpper && t_after_12 >= (int)segLower && t_after_12 <= (int)segUpper);
		    
		    func_decl rho_12 = function("rho_12", c.int_sort(), c.int_sort());
		    func_decl rho_primed_12 = function("rho_primed_12", c.real_sort(), c.real_sort());
		    
		    func_decl rho_21 = function("rho_21", c.int_sort(), c.int_sort());
		    func_decl rho_primed_21 = function("rho_primed_21", c.real_sort(), c.real_sort());
		    
		    expr pwl_12 = c.int_const("pwl_12");
		    s.add(pwl_12 >= (int)segLower + 1 && pwl_12 <= (int)segUpper);
		    
		    expr pwl_21 = c.int_const("pwl_21");
		    s.add(pwl_21 >= (int)segLower + 1 && pwl_21 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_12(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_12(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_21(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_21(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_12, t_after_12, implies(((t_before_12 < t_after_12) && (t_before_12 >= (int)segLower + 1) && (t_before_12 <= (int)segUpper) && (t_after_12 >= (int)segLower) && (t_after_12 <= (int)segUpper)), ((rho_12(t_before_12) < rho_12(t_after_12)) && (rho_21(t_before_12) < rho_21(t_after_12))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_2, implies(((rho_12(pred_1) == pred_2) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_2 >= (int)segLower) && (pred_2 <= (int)segUpper)), (c.real_val(delta) <= (((a_2_x(pred_2) - a_1_x(pred_1)) * (a_2_x(pred_2) - a_1_x(pred_1))) + ((a_2_y(pred_2) - a_1_y(pred_1)) * (a_2_y(pred_2) - a_1_y(pred_1))) + ((a_2_z(pred_2) - a_1_z(pred_1)) * (a_2_z(pred_2) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_12, implies(((pwl_12 >= (int)segLower + 1) && (pwl_12 <= (int)segUpper)), (rho_primed_12(pwl_12) == rho_12(c.int_val(pwl_12)) + ((pwl_12 - c.int_val(pwl_12)) * (rho_12(c.int_val(pwl_12) + 1) - rho_12(c.int_val(pwl_12))))))));
			s.add(forall(pwl_21, implies(((pwl_21 >= (int)segLower + 1) && (pwl_21 <= (int)segUpper)), (rho_primed_21(pwl_21) == rho_21(c.int_val(pwl_21)) + ((pwl_21 - c.int_val(pwl_21)) * (rho_21(c.int_val(pwl_21) + 1) - rho_21(c.int_val(pwl_21))))))));
			
			//inverse re-timing
			s.add(forall(t_12, implies(((t_12 >= (int)segLower) && (t_12 <= (int)segUpper)), (rho_21(rho_12(t_12)) == t_12))));

			// ================ AGENT 1 AND AGENT 2 END ================ //
			
			// =============== AGENT 1 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_13 = c.int_const("t_13");
		    s.add(t_13 >= (int)segLower + 1 && t_13 <= (int)segUpper);
		    
		    expr t_before_13 = c.int_const("t_before_13");
		    expr t_after_13 = c.int_const("t_after_13");
		    s.add(t_before_13 >= (int)segLower + 1 && t_before_13 <= (int)segUpper && t_after_13 >= (int)segLower && t_after_13 <= (int)segUpper);
		    
		    func_decl rho_13 = function("rho_13", c.int_sort(), c.int_sort());
		    func_decl rho_primed_13 = function("rho_primed_13", c.real_sort(), c.real_sort());
		    
		    func_decl rho_31 = function("rho_31", c.int_sort(), c.int_sort());
		    func_decl rho_primed_31 = function("rho_primed_31", c.real_sort(), c.real_sort());
		    
		    expr pwl_13 = c.int_const("pwl_13");
		    s.add(pwl_13 >= (int)segLower + 1 && pwl_13 <= (int)segUpper);
		    
		    expr pwl_31 = c.int_const("pwl_31");
		    s.add(pwl_31 >= (int)segLower + 1 && pwl_31 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_13(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_13(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_31(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_31(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_13, t_after_13, implies(((t_before_13 < t_after_13) && (t_before_13 >= (int)segLower + 1) && (t_before_13 <= (int)segUpper) && (t_after_13 >= (int)segLower) && (t_after_13 <= (int)segUpper)), ((rho_13(t_before_13) < rho_13(t_after_13)) && (rho_31(t_before_13) < rho_31(t_after_13))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_3, implies(((rho_13(pred_1) == pred_3) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_1_x(pred_1)) * (a_3_x(pred_3) - a_1_x(pred_1))) + ((a_3_y(pred_3) - a_1_y(pred_1)) * (a_3_y(pred_3) - a_1_y(pred_1))) + ((a_3_z(pred_3) - a_1_z(pred_1)) * (a_3_z(pred_3) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_13, implies(((pwl_13 >= (int)segLower + 1) && (pwl_13 <= (int)segUpper)), (rho_primed_13(pwl_13) == rho_13(c.int_val(pwl_13)) + ((pwl_13 - c.int_val(pwl_13)) * (rho_13(c.int_val(pwl_13) + 1) - rho_13(c.int_val(pwl_13))))))));
			s.add(forall(pwl_31, implies(((pwl_31 >= (int)segLower + 1) && (pwl_31 <= (int)segUpper)), (rho_primed_31(pwl_31) == rho_31(c.int_val(pwl_31)) + ((pwl_31 - c.int_val(pwl_31)) * (rho_31(c.int_val(pwl_31) + 1) - rho_31(c.int_val(pwl_31))))))));
			
			//inverse re-timing
			s.add(forall(t_13, implies(((t_13 >= (int)segLower) && (t_13 <= (int)segUpper)), (rho_31(rho_13(t_13)) == t_13))));

			// ================ AGENT 1 AND AGENT 3 END ================ //
			
			// =============== AGENT 1 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_14 = c.int_const("t_14");
		    s.add(t_14 >= (int)segLower + 1 && t_14 <= (int)segUpper);
		    
		    expr t_before_14 = c.int_const("t_before_14");
		    expr t_after_14 = c.int_const("t_after_14");
		    s.add(t_before_14 >= (int)segLower + 1 && t_before_14 <= (int)segUpper && t_after_14 >= (int)segLower && t_after_14 <= (int)segUpper);
		    
		    func_decl rho_14 = function("rho_14", c.int_sort(), c.int_sort());
		    func_decl rho_primed_14 = function("rho_primed_14", c.real_sort(), c.real_sort());
		    
		    func_decl rho_41 = function("rho_41", c.int_sort(), c.int_sort());
		    func_decl rho_primed_41 = function("rho_primed_41", c.real_sort(), c.real_sort());
		    
		    expr pwl_14 = c.int_const("pwl_14");
		    s.add(pwl_14 >= (int)segLower + 1 && pwl_14 <= (int)segUpper);
		    
		    expr pwl_41 = c.int_const("pwl_41");
		    s.add(pwl_41 >= (int)segLower + 1 && pwl_41 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_14(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_14(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_41(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_41(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_14, t_after_14, implies(((t_before_14 < t_after_14) && (t_before_14 >= (int)segLower + 1) && (t_before_14 <= (int)segUpper) && (t_after_14 >= (int)segLower) && (t_after_14 <= (int)segUpper)), ((rho_14(t_before_14) < rho_14(t_after_14)) && (rho_41(t_before_14) < rho_41(t_after_14))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_4, implies(((rho_14(pred_1) == pred_4) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_1_x(pred_1)) * (a_4_x(pred_4) - a_1_x(pred_1))) + ((a_4_y(pred_4) - a_1_y(pred_1)) * (a_4_y(pred_4) - a_1_y(pred_1))) + ((a_4_z(pred_4) - a_1_z(pred_1)) * (a_4_z(pred_4) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_14, implies(((pwl_14 >= (int)segLower + 1) && (pwl_14 <= (int)segUpper)), (rho_primed_14(pwl_14) == rho_14(c.int_val(pwl_14)) + ((pwl_14 - c.int_val(pwl_14)) * (rho_14(c.int_val(pwl_14) + 1) - rho_14(c.int_val(pwl_14))))))));
			s.add(forall(pwl_41, implies(((pwl_41 >= (int)segLower + 1) && (pwl_41 <= (int)segUpper)), (rho_primed_41(pwl_41) == rho_41(c.int_val(pwl_41)) + ((pwl_41 - c.int_val(pwl_41)) * (rho_41(c.int_val(pwl_41) + 1) - rho_41(c.int_val(pwl_41))))))));
			
			//inverse re-timing
			s.add(forall(t_14, implies(((t_14 >= (int)segLower) && (t_14 <= (int)segUpper)), (rho_41(rho_14(t_14)) == t_14))));

			// ================ AGENT 1 AND AGENT 4 END ================ //
			
			// =============== AGENT 1 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_15 = c.int_const("t_15");
		    s.add(t_15 >= (int)segLower + 1 && t_15 <= (int)segUpper);
		    
		    expr t_before_15 = c.int_const("t_before_15");
		    expr t_after_15 = c.int_const("t_after_15");
		    s.add(t_before_15 >= (int)segLower + 1 && t_before_15 <= (int)segUpper && t_after_15 >= (int)segLower && t_after_15 <= (int)segUpper);
		    
		    func_decl rho_15 = function("rho_15", c.int_sort(), c.int_sort());
		    func_decl rho_primed_15 = function("rho_primed_15", c.real_sort(), c.real_sort());
		    
		    func_decl rho_51 = function("rho_51", c.int_sort(), c.int_sort());
		    func_decl rho_primed_51 = function("rho_primed_51", c.real_sort(), c.real_sort());
		    
		    expr pwl_15 = c.int_const("pwl_15");
		    s.add(pwl_15 >= (int)segLower + 1 && pwl_15 <= (int)segUpper);
		    
		    expr pwl_51 = c.int_const("pwl_51");
		    s.add(pwl_51 >= (int)segLower + 1 && pwl_51 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_15(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_15(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_51(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_51(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_15, t_after_15, implies(((t_before_15 < t_after_15) && (t_before_15 >= (int)segLower + 1) && (t_before_15 <= (int)segUpper) && (t_after_15 >= (int)segLower) && (t_after_15 <= (int)segUpper)), ((rho_15(t_before_15) < rho_15(t_after_15)) && (rho_51(t_before_15) < rho_51(t_after_15))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_5, implies(((rho_15(pred_1) == pred_5) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_1_x(pred_1)) * (a_5_x(pred_5) - a_1_x(pred_1))) + ((a_5_y(pred_5) - a_1_y(pred_1)) * (a_5_y(pred_5) - a_1_y(pred_1))) + ((a_5_z(pred_5) - a_1_z(pred_1)) * (a_5_z(pred_5) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_15, implies(((pwl_15 >= (int)segLower + 1) && (pwl_15 <= (int)segUpper)), (rho_primed_15(pwl_15) == rho_15(c.int_val(pwl_15)) + ((pwl_15 - c.int_val(pwl_15)) * (rho_15(c.int_val(pwl_15) + 1) - rho_15(c.int_val(pwl_15))))))));
			s.add(forall(pwl_51, implies(((pwl_51 >= (int)segLower + 1) && (pwl_51 <= (int)segUpper)), (rho_primed_51(pwl_51) == rho_51(c.int_val(pwl_51)) + ((pwl_51 - c.int_val(pwl_51)) * (rho_51(c.int_val(pwl_51) + 1) - rho_51(c.int_val(pwl_51))))))));
			
			//inverse re-timing
			s.add(forall(t_15, implies(((t_15 >= (int)segLower) && (t_15 <= (int)segUpper)), (rho_51(rho_15(t_15)) == t_15))));

			// ================ AGENT 1 AND AGENT 5 END ================ //
			
			// =============== AGENT 1 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_16 = c.int_const("t_16");
		    s.add(t_16 >= (int)segLower + 1 && t_16 <= (int)segUpper);
		    
		    expr t_before_16 = c.int_const("t_before_16");
		    expr t_after_16 = c.int_const("t_after_16");
		    s.add(t_before_16 >= (int)segLower + 1 && t_before_16 <= (int)segUpper && t_after_16 >= (int)segLower && t_after_16 <= (int)segUpper);
		    
		    func_decl rho_16 = function("rho_16", c.int_sort(), c.int_sort());
		    func_decl rho_primed_16 = function("rho_primed_16", c.real_sort(), c.real_sort());
		    
		    func_decl rho_61 = function("rho_61", c.int_sort(), c.int_sort());
		    func_decl rho_primed_61 = function("rho_primed_61", c.real_sort(), c.real_sort());
		    
		    expr pwl_16 = c.int_const("pwl_16");
		    s.add(pwl_16 >= (int)segLower + 1 && pwl_16 <= (int)segUpper);
		    
		    expr pwl_61 = c.int_const("pwl_61");
		    s.add(pwl_61 >= (int)segLower + 1 && pwl_61 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_16(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_16(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_61(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_61(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_16, t_after_16, implies(((t_before_16 < t_after_16) && (t_before_16 >= (int)segLower + 1) && (t_before_16 <= (int)segUpper) && (t_after_16 >= (int)segLower) && (t_after_16 <= (int)segUpper)), ((rho_16(t_before_16) < rho_16(t_after_16)) && (rho_61(t_before_16) < rho_61(t_after_16))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_6, implies(((rho_16(pred_1) == pred_6) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_1_x(pred_1)) * (a_6_x(pred_6) - a_1_x(pred_1))) + ((a_6_y(pred_6) - a_1_y(pred_1)) * (a_6_y(pred_6) - a_1_y(pred_1))) + ((a_6_z(pred_6) - a_1_z(pred_1)) * (a_6_z(pred_6) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_16, implies(((pwl_16 >= (int)segLower + 1) && (pwl_16 <= (int)segUpper)), (rho_primed_16(pwl_16) == rho_16(c.int_val(pwl_16)) + ((pwl_16 - c.int_val(pwl_16)) * (rho_16(c.int_val(pwl_16) + 1) - rho_16(c.int_val(pwl_16))))))));
			s.add(forall(pwl_61, implies(((pwl_61 >= (int)segLower + 1) && (pwl_61 <= (int)segUpper)), (rho_primed_61(pwl_61) == rho_61(c.int_val(pwl_61)) + ((pwl_61 - c.int_val(pwl_61)) * (rho_61(c.int_val(pwl_61) + 1) - rho_61(c.int_val(pwl_61))))))));
			
			//inverse re-timing
			s.add(forall(t_16, implies(((t_16 >= (int)segLower) && (t_16 <= (int)segUpper)), (rho_61(rho_16(t_16)) == t_16))));

			// ================ AGENT 1 AND AGENT 6 END ================ //
			
			// =============== AGENT 1 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_17 = c.int_const("t_17");
		    s.add(t_17 >= (int)segLower + 1 && t_17 <= (int)segUpper);
		    
		    expr t_before_17 = c.int_const("t_before_17");
		    expr t_after_17 = c.int_const("t_after_17");
		    s.add(t_before_17 >= (int)segLower + 1 && t_before_17 <= (int)segUpper && t_after_17 >= (int)segLower && t_after_17 <= (int)segUpper);
		    
		    func_decl rho_17 = function("rho_17", c.int_sort(), c.int_sort());
		    func_decl rho_primed_17 = function("rho_primed_17", c.real_sort(), c.real_sort());
		    
		    func_decl rho_71 = function("rho_71", c.int_sort(), c.int_sort());
		    func_decl rho_primed_71 = function("rho_primed_71", c.real_sort(), c.real_sort());
		    
		    expr pwl_17 = c.int_const("pwl_17");
		    s.add(pwl_17 >= (int)segLower + 1 && pwl_17 <= (int)segUpper);
		    
		    expr pwl_71 = c.int_const("pwl_71");
		    s.add(pwl_71 >= (int)segLower + 1 && pwl_71 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_17(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_17(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_71(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_71(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_17, t_after_17, implies(((t_before_17 < t_after_17) && (t_before_17 >= (int)segLower + 1) && (t_before_17 <= (int)segUpper) && (t_after_17 >= (int)segLower) && (t_after_17 <= (int)segUpper)), ((rho_17(t_before_17) < rho_17(t_after_17)) && (rho_71(t_before_17) < rho_71(t_after_17))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_7, implies(((rho_17(pred_1) == pred_7) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_1_x(pred_1)) * (a_7_x(pred_7) - a_1_x(pred_1))) + ((a_7_y(pred_7) - a_1_y(pred_1)) * (a_7_y(pred_7) - a_1_y(pred_1))) + ((a_7_z(pred_7) - a_1_z(pred_1)) * (a_7_z(pred_7) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_17, implies(((pwl_17 >= (int)segLower + 1) && (pwl_17 <= (int)segUpper)), (rho_primed_17(pwl_17) == rho_17(c.int_val(pwl_17)) + ((pwl_17 - c.int_val(pwl_17)) * (rho_17(c.int_val(pwl_17) + 1) - rho_17(c.int_val(pwl_17))))))));
			s.add(forall(pwl_71, implies(((pwl_71 >= (int)segLower + 1) && (pwl_71 <= (int)segUpper)), (rho_primed_71(pwl_71) == rho_71(c.int_val(pwl_71)) + ((pwl_71 - c.int_val(pwl_71)) * (rho_71(c.int_val(pwl_71) + 1) - rho_71(c.int_val(pwl_71))))))));
			
			//inverse re-timing
			s.add(forall(t_17, implies(((t_17 >= (int)segLower) && (t_17 <= (int)segUpper)), (rho_71(rho_17(t_17)) == t_17))));

			// ================ AGENT 1 AND AGENT 7 END ================ //
			
			// =============== AGENT 1 AND AGENT 8 START =============== //
			
			//agent pair smt variables
			expr t_18 = c.int_const("t_18");
		    s.add(t_18 >= (int)segLower + 1 && t_18 <= (int)segUpper);
		    
		    expr t_before_18 = c.int_const("t_before_18");
		    expr t_after_18 = c.int_const("t_after_18");
		    s.add(t_before_18 >= (int)segLower + 1 && t_before_18 <= (int)segUpper && t_after_18 >= (int)segLower && t_after_18 <= (int)segUpper);
		    
		    func_decl rho_18 = function("rho_18", c.int_sort(), c.int_sort());
		    func_decl rho_primed_18 = function("rho_primed_18", c.real_sort(), c.real_sort());
		    
		    func_decl rho_81 = function("rho_81", c.int_sort(), c.int_sort());
		    func_decl rho_primed_81 = function("rho_primed_81", c.real_sort(), c.real_sort());
		    
		    expr pwl_18 = c.int_const("pwl_18");
		    s.add(pwl_18 >= (int)segLower + 1 && pwl_18 <= (int)segUpper);
		    
		    expr pwl_81 = c.int_const("pwl_81");
		    s.add(pwl_81 >= (int)segLower + 1 && pwl_81 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_18(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_18(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_81(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_81(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_18, t_after_18, implies(((t_before_18 < t_after_18) && (t_before_18 >= (int)segLower + 1) && (t_before_18 <= (int)segUpper) && (t_after_18 >= (int)segLower) && (t_after_18 <= (int)segUpper)), ((rho_18(t_before_18) < rho_18(t_after_18)) && (rho_81(t_before_18) < rho_81(t_after_18))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_8, implies(((rho_18(pred_1) == pred_8) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_8 >= (int)segLower) && (pred_8 <= (int)segUpper)), (c.real_val(delta) <= (((a_8_x(pred_8) - a_1_x(pred_1)) * (a_8_x(pred_8) - a_1_x(pred_1))) + ((a_8_y(pred_8) - a_1_y(pred_1)) * (a_8_y(pred_8) - a_1_y(pred_1))) + ((a_8_z(pred_8) - a_1_z(pred_1)) * (a_8_z(pred_8) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_18, implies(((pwl_18 >= (int)segLower + 1) && (pwl_18 <= (int)segUpper)), (rho_primed_18(pwl_18) == rho_18(c.int_val(pwl_18)) + ((pwl_18 - c.int_val(pwl_18)) * (rho_18(c.int_val(pwl_18) + 1) - rho_18(c.int_val(pwl_18))))))));
			s.add(forall(pwl_81, implies(((pwl_81 >= (int)segLower + 1) && (pwl_81 <= (int)segUpper)), (rho_primed_81(pwl_81) == rho_81(c.int_val(pwl_81)) + ((pwl_81 - c.int_val(pwl_81)) * (rho_81(c.int_val(pwl_81) + 1) - rho_81(c.int_val(pwl_81))))))));
			
			//inverse re-timing
			s.add(forall(t_18, implies(((t_18 >= (int)segLower) && (t_18 <= (int)segUpper)), (rho_81(rho_18(t_18)) == t_18))));

			// ================ AGENT 1 AND AGENT 8 END ================ //
			
			// =============== AGENT 2 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_23 = c.int_const("t_23");
		    s.add(t_23 >= (int)segLower + 1 && t_23 <= (int)segUpper);
		    
		    expr t_before_23 = c.int_const("t_before_23");
		    expr t_after_23 = c.int_const("t_after_23");
		    s.add(t_before_23 >= (int)segLower + 1 && t_before_23 <= (int)segUpper && t_after_23 >= (int)segLower && t_after_23 <= (int)segUpper);
		    
		    func_decl rho_23 = function("rho_23", c.int_sort(), c.int_sort());
		    func_decl rho_primed_23 = function("rho_primed_23", c.real_sort(), c.real_sort());
		    
		    func_decl rho_32 = function("rho_32", c.int_sort(), c.int_sort());
		    func_decl rho_primed_32 = function("rho_primed_32", c.real_sort(), c.real_sort());
		    
		    expr pwl_23 = c.int_const("pwl_23");
		    s.add(pwl_23 >= (int)segLower + 1 && pwl_23 <= (int)segUpper);
		    
		    expr pwl_32 = c.int_const("pwl_32");
		    s.add(pwl_32 >= (int)segLower + 1 && pwl_32 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_23(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_23(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_32(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_32(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_23, t_after_23, implies(((t_before_23 < t_after_23) && (t_before_23 >= (int)segLower + 1) && (t_before_23 <= (int)segUpper) && (t_after_23 >= (int)segLower) && (t_after_23 <= (int)segUpper)), ((rho_23(t_before_23) < rho_23(t_after_23)) && (rho_32(t_before_23) < rho_32(t_after_23))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_3, implies(((rho_23(pred_2) == pred_3) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_2_x(pred_2)) * (a_3_x(pred_3) - a_2_x(pred_2))) + ((a_3_y(pred_3) - a_2_y(pred_2)) * (a_3_y(pred_3) - a_2_y(pred_2))) + ((a_3_z(pred_3) - a_2_z(pred_2)) * (a_3_z(pred_3) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_23, implies(((pwl_23 >= (int)segLower + 1) && (pwl_23 <= (int)segUpper)), (rho_primed_23(pwl_23) == rho_23(c.int_val(pwl_23)) + ((pwl_23 - c.int_val(pwl_23)) * (rho_23(c.int_val(pwl_23) + 1) - rho_23(c.int_val(pwl_23))))))));
			s.add(forall(pwl_32, implies(((pwl_32 >= (int)segLower + 1) && (pwl_32 <= (int)segUpper)), (rho_primed_32(pwl_32) == rho_32(c.int_val(pwl_32)) + ((pwl_32 - c.int_val(pwl_32)) * (rho_32(c.int_val(pwl_32) + 1) - rho_32(c.int_val(pwl_32))))))));
			
			//inverse re-timing
			s.add(forall(t_23, implies(((t_23 >= (int)segLower) && (t_23 <= (int)segUpper)), (rho_32(rho_23(t_23)) == t_23))));

			// ================ AGENT 2 AND AGENT 3 END ================ //
			
			// =============== AGENT 2 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_24 = c.int_const("t_24");
		    s.add(t_24 >= (int)segLower + 1 && t_24 <= (int)segUpper);
		    
		    expr t_before_24 = c.int_const("t_before_24");
		    expr t_after_24 = c.int_const("t_after_24");
		    s.add(t_before_24 >= (int)segLower + 1 && t_before_24 <= (int)segUpper && t_after_24 >= (int)segLower && t_after_24 <= (int)segUpper);
		    
		    func_decl rho_24 = function("rho_24", c.int_sort(), c.int_sort());
		    func_decl rho_primed_24 = function("rho_primed_24", c.real_sort(), c.real_sort());
		    
		    func_decl rho_42 = function("rho_42", c.int_sort(), c.int_sort());
		    func_decl rho_primed_42 = function("rho_primed_42", c.real_sort(), c.real_sort());
		    
		    expr pwl_24 = c.int_const("pwl_24");
		    s.add(pwl_24 >= (int)segLower + 1 && pwl_24 <= (int)segUpper);
		    
		    expr pwl_42 = c.int_const("pwl_42");
		    s.add(pwl_42 >= (int)segLower + 1 && pwl_42 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_24(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_24(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_42(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_42(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_24, t_after_24, implies(((t_before_24 < t_after_24) && (t_before_24 >= (int)segLower + 1) && (t_before_24 <= (int)segUpper) && (t_after_24 >= (int)segLower) && (t_after_24 <= (int)segUpper)), ((rho_24(t_before_24) < rho_24(t_after_24)) && (rho_42(t_before_24) < rho_42(t_after_24))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_4, implies(((rho_24(pred_2) == pred_4) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_2_x(pred_2)) * (a_4_x(pred_4) - a_2_x(pred_2))) + ((a_4_y(pred_4) - a_2_y(pred_2)) * (a_4_y(pred_4) - a_2_y(pred_2))) + ((a_4_z(pred_4) - a_2_z(pred_2)) * (a_4_z(pred_4) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_24, implies(((pwl_24 >= (int)segLower + 1) && (pwl_24 <= (int)segUpper)), (rho_primed_24(pwl_24) == rho_24(c.int_val(pwl_24)) + ((pwl_24 - c.int_val(pwl_24)) * (rho_24(c.int_val(pwl_24) + 1) - rho_24(c.int_val(pwl_24))))))));
			s.add(forall(pwl_42, implies(((pwl_42 >= (int)segLower + 1) && (pwl_42 <= (int)segUpper)), (rho_primed_42(pwl_42) == rho_42(c.int_val(pwl_42)) + ((pwl_42 - c.int_val(pwl_42)) * (rho_42(c.int_val(pwl_42) + 1) - rho_42(c.int_val(pwl_42))))))));
			
			//inverse re-timing
			s.add(forall(t_24, implies(((t_24 >= (int)segLower) && (t_24 <= (int)segUpper)), (rho_42(rho_24(t_24)) == t_24))));

			// ================ AGENT 2 AND AGENT 4 END ================ //
			
			// =============== AGENT 2 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_25 = c.int_const("t_25");
		    s.add(t_25 >= (int)segLower + 1 && t_25 <= (int)segUpper);
		    
		    expr t_before_25 = c.int_const("t_before_25");
		    expr t_after_25 = c.int_const("t_after_25");
		    s.add(t_before_25 >= (int)segLower + 1 && t_before_25 <= (int)segUpper && t_after_25 >= (int)segLower && t_after_25 <= (int)segUpper);
		    
		    func_decl rho_25 = function("rho_25", c.int_sort(), c.int_sort());
		    func_decl rho_primed_25 = function("rho_primed_25", c.real_sort(), c.real_sort());
		    
		    func_decl rho_52 = function("rho_52", c.int_sort(), c.int_sort());
		    func_decl rho_primed_52 = function("rho_primed_52", c.real_sort(), c.real_sort());
		    
		    expr pwl_25 = c.int_const("pwl_25");
		    s.add(pwl_25 >= (int)segLower + 1 && pwl_25 <= (int)segUpper);
		    
		    expr pwl_52 = c.int_const("pwl_52");
		    s.add(pwl_52 >= (int)segLower + 1 && pwl_52 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_25(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_25(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_52(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_52(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_25, t_after_25, implies(((t_before_25 < t_after_25) && (t_before_25 >= (int)segLower + 1) && (t_before_25 <= (int)segUpper) && (t_after_25 >= (int)segLower) && (t_after_25 <= (int)segUpper)), ((rho_25(t_before_25) < rho_25(t_after_25)) && (rho_52(t_before_25) < rho_52(t_after_25))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_5, implies(((rho_25(pred_2) == pred_5) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_2_x(pred_2)) * (a_5_x(pred_5) - a_2_x(pred_2))) + ((a_5_y(pred_5) - a_2_y(pred_2)) * (a_5_y(pred_5) - a_2_y(pred_2))) + ((a_5_z(pred_5) - a_2_z(pred_2)) * (a_5_z(pred_5) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_25, implies(((pwl_25 >= (int)segLower + 1) && (pwl_25 <= (int)segUpper)), (rho_primed_25(pwl_25) == rho_25(c.int_val(pwl_25)) + ((pwl_25 - c.int_val(pwl_25)) * (rho_25(c.int_val(pwl_25) + 1) - rho_25(c.int_val(pwl_25))))))));
			s.add(forall(pwl_52, implies(((pwl_52 >= (int)segLower + 1) && (pwl_52 <= (int)segUpper)), (rho_primed_52(pwl_52) == rho_52(c.int_val(pwl_52)) + ((pwl_52 - c.int_val(pwl_52)) * (rho_52(c.int_val(pwl_52) + 1) - rho_52(c.int_val(pwl_52))))))));
			
			//inverse re-timing
			s.add(forall(t_25, implies(((t_25 >= (int)segLower) && (t_25 <= (int)segUpper)), (rho_52(rho_25(t_25)) == t_25))));

			// ================ AGENT 2 AND AGENT 5 END ================ //
			
			// =============== AGENT 2 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_26 = c.int_const("t_26");
		    s.add(t_26 >= (int)segLower + 1 && t_26 <= (int)segUpper);
		    
		    expr t_before_26 = c.int_const("t_before_26");
		    expr t_after_26 = c.int_const("t_after_26");
		    s.add(t_before_26 >= (int)segLower + 1 && t_before_26 <= (int)segUpper && t_after_26 >= (int)segLower && t_after_26 <= (int)segUpper);
		    
		    func_decl rho_26 = function("rho_26", c.int_sort(), c.int_sort());
		    func_decl rho_primed_26 = function("rho_primed_26", c.real_sort(), c.real_sort());
		    
		    func_decl rho_62 = function("rho_62", c.int_sort(), c.int_sort());
		    func_decl rho_primed_62 = function("rho_primed_62", c.real_sort(), c.real_sort());
		    
		    expr pwl_26 = c.int_const("pwl_26");
		    s.add(pwl_26 >= (int)segLower + 1 && pwl_26 <= (int)segUpper);
		    
		    expr pwl_62 = c.int_const("pwl_62");
		    s.add(pwl_62 >= (int)segLower + 1 && pwl_62 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_26(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_26(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_62(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_62(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_26, t_after_26, implies(((t_before_26 < t_after_26) && (t_before_26 >= (int)segLower + 1) && (t_before_26 <= (int)segUpper) && (t_after_26 >= (int)segLower) && (t_after_26 <= (int)segUpper)), ((rho_26(t_before_26) < rho_26(t_after_26)) && (rho_62(t_before_26) < rho_62(t_after_26))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_6, implies(((rho_26(pred_2) == pred_6) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_2_x(pred_2)) * (a_6_x(pred_6) - a_2_x(pred_2))) + ((a_6_y(pred_6) - a_2_y(pred_2)) * (a_6_y(pred_6) - a_2_y(pred_2))) + ((a_6_z(pred_6) - a_2_z(pred_2)) * (a_6_z(pred_6) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_26, implies(((pwl_26 >= (int)segLower + 1) && (pwl_26 <= (int)segUpper)), (rho_primed_26(pwl_26) == rho_26(c.int_val(pwl_26)) + ((pwl_26 - c.int_val(pwl_26)) * (rho_26(c.int_val(pwl_26) + 1) - rho_26(c.int_val(pwl_26))))))));
			s.add(forall(pwl_62, implies(((pwl_62 >= (int)segLower + 1) && (pwl_62 <= (int)segUpper)), (rho_primed_62(pwl_62) == rho_62(c.int_val(pwl_62)) + ((pwl_62 - c.int_val(pwl_62)) * (rho_62(c.int_val(pwl_62) + 1) - rho_62(c.int_val(pwl_62))))))));
			
			//inverse re-timing
			s.add(forall(t_26, implies(((t_26 >= (int)segLower) && (t_26 <= (int)segUpper)), (rho_62(rho_26(t_26)) == t_26))));

			// ================ AGENT 2 AND AGENT 6 END ================ //
			
			// =============== AGENT 2 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_27 = c.int_const("t_27");
		    s.add(t_27 >= (int)segLower + 1 && t_27 <= (int)segUpper);
		    
		    expr t_before_27 = c.int_const("t_before_27");
		    expr t_after_27 = c.int_const("t_after_27");
		    s.add(t_before_27 >= (int)segLower + 1 && t_before_27 <= (int)segUpper && t_after_27 >= (int)segLower && t_after_27 <= (int)segUpper);
		    
		    func_decl rho_27 = function("rho_27", c.int_sort(), c.int_sort());
		    func_decl rho_primed_27 = function("rho_primed_27", c.real_sort(), c.real_sort());
		    
		    func_decl rho_72 = function("rho_72", c.int_sort(), c.int_sort());
		    func_decl rho_primed_72 = function("rho_primed_72", c.real_sort(), c.real_sort());
		    
		    expr pwl_27 = c.int_const("pwl_27");
		    s.add(pwl_27 >= (int)segLower + 1 && pwl_27 <= (int)segUpper);
		    
		    expr pwl_72 = c.int_const("pwl_72");
		    s.add(pwl_72 >= (int)segLower + 1 && pwl_72 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_27(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_27(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_72(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_72(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_27, t_after_27, implies(((t_before_27 < t_after_27) && (t_before_27 >= (int)segLower + 1) && (t_before_27 <= (int)segUpper) && (t_after_27 >= (int)segLower) && (t_after_27 <= (int)segUpper)), ((rho_27(t_before_27) < rho_27(t_after_27)) && (rho_72(t_before_27) < rho_72(t_after_27))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_7, implies(((rho_27(pred_2) == pred_7) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_2_x(pred_2)) * (a_7_x(pred_7) - a_2_x(pred_2))) + ((a_7_y(pred_7) - a_2_y(pred_2)) * (a_7_y(pred_7) - a_2_y(pred_2))) + ((a_7_z(pred_7) - a_2_z(pred_2)) * (a_7_z(pred_7) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_27, implies(((pwl_27 >= (int)segLower + 1) && (pwl_27 <= (int)segUpper)), (rho_primed_27(pwl_27) == rho_27(c.int_val(pwl_27)) + ((pwl_27 - c.int_val(pwl_27)) * (rho_27(c.int_val(pwl_27) + 1) - rho_27(c.int_val(pwl_27))))))));
			s.add(forall(pwl_72, implies(((pwl_72 >= (int)segLower + 1) && (pwl_72 <= (int)segUpper)), (rho_primed_72(pwl_72) == rho_72(c.int_val(pwl_72)) + ((pwl_72 - c.int_val(pwl_72)) * (rho_72(c.int_val(pwl_72) + 1) - rho_72(c.int_val(pwl_72))))))));
			
			//inverse re-timing
			s.add(forall(t_27, implies(((t_27 >= (int)segLower) && (t_27 <= (int)segUpper)), (rho_72(rho_27(t_27)) == t_27))));

			// ================ AGENT 2 AND AGENT 7 END ================ //
			
			// =============== AGENT 2 AND AGENT 8 START =============== //
			
			//agent pair smt variables
			expr t_28 = c.int_const("t_28");
		    s.add(t_28 >= (int)segLower + 1 && t_28 <= (int)segUpper);
		    
		    expr t_before_28 = c.int_const("t_before_28");
		    expr t_after_28 = c.int_const("t_after_28");
		    s.add(t_before_28 >= (int)segLower + 1 && t_before_28 <= (int)segUpper && t_after_28 >= (int)segLower && t_after_28 <= (int)segUpper);
		    
		    func_decl rho_28 = function("rho_28", c.int_sort(), c.int_sort());
		    func_decl rho_primed_28 = function("rho_primed_28", c.real_sort(), c.real_sort());
		    
		    func_decl rho_82 = function("rho_82", c.int_sort(), c.int_sort());
		    func_decl rho_primed_82 = function("rho_primed_82", c.real_sort(), c.real_sort());
		    
		    expr pwl_28 = c.int_const("pwl_28");
		    s.add(pwl_28 >= (int)segLower + 1 && pwl_28 <= (int)segUpper);
		    
		    expr pwl_82 = c.int_const("pwl_82");
		    s.add(pwl_82 >= (int)segLower + 1 && pwl_82 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_28(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_28(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_82(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_82(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_28, t_after_28, implies(((t_before_28 < t_after_28) && (t_before_28 >= (int)segLower + 1) && (t_before_28 <= (int)segUpper) && (t_after_28 >= (int)segLower) && (t_after_28 <= (int)segUpper)), ((rho_28(t_before_28) < rho_28(t_after_28)) && (rho_82(t_before_28) < rho_82(t_after_28))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_8, implies(((rho_28(pred_2) == pred_8) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_8 >= (int)segLower) && (pred_8 <= (int)segUpper)), (c.real_val(delta) <= (((a_8_x(pred_8) - a_2_x(pred_2)) * (a_8_x(pred_8) - a_2_x(pred_2))) + ((a_8_y(pred_8) - a_2_y(pred_2)) * (a_8_y(pred_8) - a_2_y(pred_2))) + ((a_8_z(pred_8) - a_2_z(pred_2)) * (a_8_z(pred_8) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_28, implies(((pwl_28 >= (int)segLower + 1) && (pwl_28 <= (int)segUpper)), (rho_primed_28(pwl_28) == rho_28(c.int_val(pwl_28)) + ((pwl_28 - c.int_val(pwl_28)) * (rho_28(c.int_val(pwl_28) + 1) - rho_28(c.int_val(pwl_28))))))));
			s.add(forall(pwl_82, implies(((pwl_82 >= (int)segLower + 1) && (pwl_82 <= (int)segUpper)), (rho_primed_82(pwl_82) == rho_82(c.int_val(pwl_82)) + ((pwl_82 - c.int_val(pwl_82)) * (rho_82(c.int_val(pwl_82) + 1) - rho_82(c.int_val(pwl_82))))))));
			
			//inverse re-timing
			s.add(forall(t_28, implies(((t_28 >= (int)segLower) && (t_28 <= (int)segUpper)), (rho_82(rho_28(t_28)) == t_28))));

			// ================ AGENT 2 AND AGENT 8 END ================ //
			
			// =============== AGENT 3 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_34 = c.int_const("t_34");
		    s.add(t_34 >= (int)segLower + 1 && t_34 <= (int)segUpper);
		    
		    expr t_before_34 = c.int_const("t_before_34");
		    expr t_after_34 = c.int_const("t_after_34");
		    s.add(t_before_34 >= (int)segLower + 1 && t_before_34 <= (int)segUpper && t_after_34 >= (int)segLower && t_after_34 <= (int)segUpper);
		    
		    func_decl rho_34 = function("rho_34", c.int_sort(), c.int_sort());
		    func_decl rho_primed_34 = function("rho_primed_34", c.real_sort(), c.real_sort());
		    
		    func_decl rho_43 = function("rho_43", c.int_sort(), c.int_sort());
		    func_decl rho_primed_43 = function("rho_primed_43", c.real_sort(), c.real_sort());
		    
		    expr pwl_34 = c.int_const("pwl_34");
		    s.add(pwl_34 >= (int)segLower + 1 && pwl_34 <= (int)segUpper);
		    
		    expr pwl_43 = c.int_const("pwl_43");
		    s.add(pwl_43 >= (int)segLower + 1 && pwl_43 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_34(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_34(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_43(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_43(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_34, t_after_34, implies(((t_before_34 < t_after_34) && (t_before_34 >= (int)segLower + 1) && (t_before_34 <= (int)segUpper) && (t_after_34 >= (int)segLower) && (t_after_34 <= (int)segUpper)), ((rho_34(t_before_34) < rho_34(t_after_34)) && (rho_43(t_before_34) < rho_43(t_after_34))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_4, implies(((rho_34(pred_3) == pred_4) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_3_x(pred_3)) * (a_4_x(pred_4) - a_3_x(pred_3))) + ((a_4_y(pred_4) - a_3_y(pred_3)) * (a_4_y(pred_4) - a_3_y(pred_3))) + ((a_4_z(pred_4) - a_3_z(pred_3)) * (a_4_z(pred_4) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_34, implies(((pwl_34 >= (int)segLower + 1) && (pwl_34 <= (int)segUpper)), (rho_primed_34(pwl_34) == rho_34(c.int_val(pwl_34)) + ((pwl_34 - c.int_val(pwl_34)) * (rho_34(c.int_val(pwl_34) + 1) - rho_34(c.int_val(pwl_34))))))));
			s.add(forall(pwl_43, implies(((pwl_43 >= (int)segLower + 1) && (pwl_43 <= (int)segUpper)), (rho_primed_43(pwl_43) == rho_43(c.int_val(pwl_43)) + ((pwl_43 - c.int_val(pwl_43)) * (rho_43(c.int_val(pwl_43) + 1) - rho_43(c.int_val(pwl_43))))))));
			
			//inverse re-timing
			s.add(forall(t_34, implies(((t_34 >= (int)segLower) && (t_34 <= (int)segUpper)), (rho_43(rho_34(t_34)) == t_34))));

			// ================ AGENT 3 AND AGENT 4 END ================ //
			
			// =============== AGENT 3 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_35 = c.int_const("t_35");
		    s.add(t_35 >= (int)segLower + 1 && t_35 <= (int)segUpper);
		    
		    expr t_before_35 = c.int_const("t_before_35");
		    expr t_after_35 = c.int_const("t_after_35");
		    s.add(t_before_35 >= (int)segLower + 1 && t_before_35 <= (int)segUpper && t_after_35 >= (int)segLower && t_after_35 <= (int)segUpper);
		    
		    func_decl rho_35 = function("rho_35", c.int_sort(), c.int_sort());
		    func_decl rho_primed_35 = function("rho_primed_35", c.real_sort(), c.real_sort());
		    
		    func_decl rho_53 = function("rho_53", c.int_sort(), c.int_sort());
		    func_decl rho_primed_53 = function("rho_primed_53", c.real_sort(), c.real_sort());
		    
		    expr pwl_35 = c.int_const("pwl_35");
		    s.add(pwl_35 >= (int)segLower + 1 && pwl_35 <= (int)segUpper);
		    
		    expr pwl_53 = c.int_const("pwl_53");
		    s.add(pwl_53 >= (int)segLower + 1 && pwl_53 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_35(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_35(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_53(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_53(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_35, t_after_35, implies(((t_before_35 < t_after_35) && (t_before_35 >= (int)segLower + 1) && (t_before_35 <= (int)segUpper) && (t_after_35 >= (int)segLower) && (t_after_35 <= (int)segUpper)), ((rho_35(t_before_35) < rho_35(t_after_35)) && (rho_53(t_before_35) < rho_53(t_after_35))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_5, implies(((rho_35(pred_3) == pred_5) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_3_x(pred_3)) * (a_5_x(pred_5) - a_3_x(pred_3))) + ((a_5_y(pred_5) - a_3_y(pred_3)) * (a_5_y(pred_5) - a_3_y(pred_3))) + ((a_5_z(pred_5) - a_3_z(pred_3)) * (a_5_z(pred_5) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_35, implies(((pwl_35 >= (int)segLower + 1) && (pwl_35 <= (int)segUpper)), (rho_primed_35(pwl_35) == rho_35(c.int_val(pwl_35)) + ((pwl_35 - c.int_val(pwl_35)) * (rho_35(c.int_val(pwl_35) + 1) - rho_35(c.int_val(pwl_35))))))));
			s.add(forall(pwl_53, implies(((pwl_53 >= (int)segLower + 1) && (pwl_53 <= (int)segUpper)), (rho_primed_53(pwl_53) == rho_53(c.int_val(pwl_53)) + ((pwl_53 - c.int_val(pwl_53)) * (rho_53(c.int_val(pwl_53) + 1) - rho_53(c.int_val(pwl_53))))))));
			
			//inverse re-timing
			s.add(forall(t_35, implies(((t_35 >= (int)segLower) && (t_35 <= (int)segUpper)), (rho_53(rho_35(t_35)) == t_35))));

			// ================ AGENT 3 AND AGENT 5 END ================ //
			
			// =============== AGENT 3 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_36 = c.int_const("t_36");
		    s.add(t_36 >= (int)segLower + 1 && t_36 <= (int)segUpper);
		    
		    expr t_before_36 = c.int_const("t_before_36");
		    expr t_after_36 = c.int_const("t_after_36");
		    s.add(t_before_36 >= (int)segLower + 1 && t_before_36 <= (int)segUpper && t_after_36 >= (int)segLower && t_after_36 <= (int)segUpper);
		    
		    func_decl rho_36 = function("rho_36", c.int_sort(), c.int_sort());
		    func_decl rho_primed_36 = function("rho_primed_36", c.real_sort(), c.real_sort());
		    
		    func_decl rho_63 = function("rho_63", c.int_sort(), c.int_sort());
		    func_decl rho_primed_63 = function("rho_primed_63", c.real_sort(), c.real_sort());
		    
		    expr pwl_36 = c.int_const("pwl_36");
		    s.add(pwl_36 >= (int)segLower + 1 && pwl_36 <= (int)segUpper);
		    
		    expr pwl_63 = c.int_const("pwl_63");
		    s.add(pwl_63 >= (int)segLower + 1 && pwl_63 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_36(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_36(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_63(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_63(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_36, t_after_36, implies(((t_before_36 < t_after_36) && (t_before_36 >= (int)segLower + 1) && (t_before_36 <= (int)segUpper) && (t_after_36 >= (int)segLower) && (t_after_36 <= (int)segUpper)), ((rho_36(t_before_36) < rho_36(t_after_36)) && (rho_63(t_before_36) < rho_63(t_after_36))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_6, implies(((rho_36(pred_3) == pred_6) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_3_x(pred_3)) * (a_6_x(pred_6) - a_3_x(pred_3))) + ((a_6_y(pred_6) - a_3_y(pred_3)) * (a_6_y(pred_6) - a_3_y(pred_3))) + ((a_6_z(pred_6) - a_3_z(pred_3)) * (a_6_z(pred_6) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_36, implies(((pwl_36 >= (int)segLower + 1) && (pwl_36 <= (int)segUpper)), (rho_primed_36(pwl_36) == rho_36(c.int_val(pwl_36)) + ((pwl_36 - c.int_val(pwl_36)) * (rho_36(c.int_val(pwl_36) + 1) - rho_36(c.int_val(pwl_36))))))));
			s.add(forall(pwl_63, implies(((pwl_63 >= (int)segLower + 1) && (pwl_63 <= (int)segUpper)), (rho_primed_63(pwl_63) == rho_63(c.int_val(pwl_63)) + ((pwl_63 - c.int_val(pwl_63)) * (rho_63(c.int_val(pwl_63) + 1) - rho_63(c.int_val(pwl_63))))))));
			
			//inverse re-timing
			s.add(forall(t_36, implies(((t_36 >= (int)segLower) && (t_36 <= (int)segUpper)), (rho_63(rho_36(t_36)) == t_36))));

			// ================ AGENT 3 AND AGENT 6 END ================ //
			
			// =============== AGENT 3 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_37 = c.int_const("t_37");
		    s.add(t_37 >= (int)segLower + 1 && t_37 <= (int)segUpper);
		    
		    expr t_before_37 = c.int_const("t_before_37");
		    expr t_after_37 = c.int_const("t_after_37");
		    s.add(t_before_37 >= (int)segLower + 1 && t_before_37 <= (int)segUpper && t_after_37 >= (int)segLower && t_after_37 <= (int)segUpper);
		    
		    func_decl rho_37 = function("rho_37", c.int_sort(), c.int_sort());
		    func_decl rho_primed_37 = function("rho_primed_37", c.real_sort(), c.real_sort());
		    
		    func_decl rho_73 = function("rho_73", c.int_sort(), c.int_sort());
		    func_decl rho_primed_73 = function("rho_primed_73", c.real_sort(), c.real_sort());
		    
		    expr pwl_37 = c.int_const("pwl_37");
		    s.add(pwl_37 >= (int)segLower + 1 && pwl_37 <= (int)segUpper);
		    
		    expr pwl_73 = c.int_const("pwl_73");
		    s.add(pwl_73 >= (int)segLower + 1 && pwl_73 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_37(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_37(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_73(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_73(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_37, t_after_37, implies(((t_before_37 < t_after_37) && (t_before_37 >= (int)segLower + 1) && (t_before_37 <= (int)segUpper) && (t_after_37 >= (int)segLower) && (t_after_37 <= (int)segUpper)), ((rho_37(t_before_37) < rho_37(t_after_37)) && (rho_73(t_before_37) < rho_73(t_after_37))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_7, implies(((rho_37(pred_3) == pred_7) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_3_x(pred_3)) * (a_7_x(pred_7) - a_3_x(pred_3))) + ((a_7_y(pred_7) - a_3_y(pred_3)) * (a_7_y(pred_7) - a_3_y(pred_3))) + ((a_7_z(pred_7) - a_3_z(pred_3)) * (a_7_z(pred_7) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_37, implies(((pwl_37 >= (int)segLower + 1) && (pwl_37 <= (int)segUpper)), (rho_primed_37(pwl_37) == rho_37(c.int_val(pwl_37)) + ((pwl_37 - c.int_val(pwl_37)) * (rho_37(c.int_val(pwl_37) + 1) - rho_37(c.int_val(pwl_37))))))));
			s.add(forall(pwl_73, implies(((pwl_73 >= (int)segLower + 1) && (pwl_73 <= (int)segUpper)), (rho_primed_73(pwl_73) == rho_73(c.int_val(pwl_73)) + ((pwl_73 - c.int_val(pwl_73)) * (rho_73(c.int_val(pwl_73) + 1) - rho_73(c.int_val(pwl_73))))))));
			
			//inverse re-timing
			s.add(forall(t_37, implies(((t_37 >= (int)segLower) && (t_37 <= (int)segUpper)), (rho_73(rho_37(t_37)) == t_37))));

			// ================ AGENT 3 AND AGENT 7 END ================ //
			
			// =============== AGENT 3 AND AGENT 8 START =============== //
			
			//agent pair smt variables
			expr t_38 = c.int_const("t_38");
		    s.add(t_38 >= (int)segLower + 1 && t_38 <= (int)segUpper);
		    
		    expr t_before_38 = c.int_const("t_before_38");
		    expr t_after_38 = c.int_const("t_after_38");
		    s.add(t_before_38 >= (int)segLower + 1 && t_before_38 <= (int)segUpper && t_after_38 >= (int)segLower && t_after_38 <= (int)segUpper);
		    
		    func_decl rho_38 = function("rho_38", c.int_sort(), c.int_sort());
		    func_decl rho_primed_38 = function("rho_primed_38", c.real_sort(), c.real_sort());
		    
		    func_decl rho_83 = function("rho_83", c.int_sort(), c.int_sort());
		    func_decl rho_primed_83 = function("rho_primed_83", c.real_sort(), c.real_sort());
		    
		    expr pwl_38 = c.int_const("pwl_38");
		    s.add(pwl_38 >= (int)segLower + 1 && pwl_38 <= (int)segUpper);
		    
		    expr pwl_83 = c.int_const("pwl_83");
		    s.add(pwl_83 >= (int)segLower + 1 && pwl_83 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_38(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_38(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_83(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_83(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_38, t_after_38, implies(((t_before_38 < t_after_38) && (t_before_38 >= (int)segLower + 1) && (t_before_38 <= (int)segUpper) && (t_after_38 >= (int)segLower) && (t_after_38 <= (int)segUpper)), ((rho_38(t_before_38) < rho_38(t_after_38)) && (rho_83(t_before_38) < rho_83(t_after_38))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_8, implies(((rho_38(pred_3) == pred_8) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_8 >= (int)segLower) && (pred_8 <= (int)segUpper)), (c.real_val(delta) <= (((a_8_x(pred_8) - a_3_x(pred_3)) * (a_8_x(pred_8) - a_3_x(pred_3))) + ((a_8_y(pred_8) - a_3_y(pred_3)) * (a_8_y(pred_8) - a_3_y(pred_3))) + ((a_8_z(pred_8) - a_3_z(pred_3)) * (a_8_z(pred_8) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_38, implies(((pwl_38 >= (int)segLower + 1) && (pwl_38 <= (int)segUpper)), (rho_primed_38(pwl_38) == rho_38(c.int_val(pwl_38)) + ((pwl_38 - c.int_val(pwl_38)) * (rho_38(c.int_val(pwl_38) + 1) - rho_38(c.int_val(pwl_38))))))));
			s.add(forall(pwl_83, implies(((pwl_83 >= (int)segLower + 1) && (pwl_83 <= (int)segUpper)), (rho_primed_83(pwl_83) == rho_83(c.int_val(pwl_83)) + ((pwl_83 - c.int_val(pwl_83)) * (rho_83(c.int_val(pwl_83) + 1) - rho_83(c.int_val(pwl_83))))))));
			
			//inverse re-timing
			s.add(forall(t_38, implies(((t_38 >= (int)segLower) && (t_38 <= (int)segUpper)), (rho_83(rho_38(t_38)) == t_38))));

			// ================ AGENT 3 AND AGENT 8 END ================ //
			
			// =============== AGENT 4 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_45 = c.int_const("t_45");
		    s.add(t_45 >= (int)segLower + 1 && t_45 <= (int)segUpper);
		    
		    expr t_before_45 = c.int_const("t_before_45");
		    expr t_after_45 = c.int_const("t_after_45");
		    s.add(t_before_45 >= (int)segLower + 1 && t_before_45 <= (int)segUpper && t_after_45 >= (int)segLower && t_after_45 <= (int)segUpper);
		    
		    func_decl rho_45 = function("rho_45", c.int_sort(), c.int_sort());
		    func_decl rho_primed_45 = function("rho_primed_45", c.real_sort(), c.real_sort());
		    
		    func_decl rho_54 = function("rho_54", c.int_sort(), c.int_sort());
		    func_decl rho_primed_54 = function("rho_primed_54", c.real_sort(), c.real_sort());
		    
		    expr pwl_45 = c.int_const("pwl_45");
		    s.add(pwl_45 >= (int)segLower + 1 && pwl_45 <= (int)segUpper);
		    
		    expr pwl_54 = c.int_const("pwl_54");
		    s.add(pwl_54 >= (int)segLower + 1 && pwl_54 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_45(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_45(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_54(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_54(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_45, t_after_45, implies(((t_before_45 < t_after_45) && (t_before_45 >= (int)segLower + 1) && (t_before_45 <= (int)segUpper) && (t_after_45 >= (int)segLower) && (t_after_45 <= (int)segUpper)), ((rho_45(t_before_45) < rho_45(t_after_45)) && (rho_54(t_before_45) < rho_54(t_after_45))))));
			
			//mutual separation constraint
			s.add(forall(pred_4, pred_5, implies(((rho_45(pred_4) == pred_5) && (pred_4 >= (int)segLower + 1) && (pred_4 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_4_x(pred_4)) * (a_5_x(pred_5) - a_4_x(pred_4))) + ((a_5_y(pred_5) - a_4_y(pred_4)) * (a_5_y(pred_5) - a_4_y(pred_4))) + ((a_5_z(pred_5) - a_4_z(pred_4)) * (a_5_z(pred_5) - a_4_z(pred_4))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_45, implies(((pwl_45 >= (int)segLower + 1) && (pwl_45 <= (int)segUpper)), (rho_primed_45(pwl_45) == rho_45(c.int_val(pwl_45)) + ((pwl_45 - c.int_val(pwl_45)) * (rho_45(c.int_val(pwl_45) + 1) - rho_45(c.int_val(pwl_45))))))));
			s.add(forall(pwl_54, implies(((pwl_54 >= (int)segLower + 1) && (pwl_54 <= (int)segUpper)), (rho_primed_54(pwl_54) == rho_54(c.int_val(pwl_54)) + ((pwl_54 - c.int_val(pwl_54)) * (rho_54(c.int_val(pwl_54) + 1) - rho_54(c.int_val(pwl_54))))))));
			
			//inverse re-timing
			s.add(forall(t_45, implies(((t_45 >= (int)segLower) && (t_45 <= (int)segUpper)), (rho_54(rho_45(t_45)) == t_45))));

			// ================ AGENT 4 AND AGENT 5 END ================ //
			
			// =============== AGENT 4 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_46 = c.int_const("t_46");
		    s.add(t_46 >= (int)segLower + 1 && t_46 <= (int)segUpper);
		    
		    expr t_before_46 = c.int_const("t_before_46");
		    expr t_after_46 = c.int_const("t_after_46");
		    s.add(t_before_46 >= (int)segLower + 1 && t_before_46 <= (int)segUpper && t_after_46 >= (int)segLower && t_after_46 <= (int)segUpper);
		    
		    func_decl rho_46 = function("rho_46", c.int_sort(), c.int_sort());
		    func_decl rho_primed_46 = function("rho_primed_46", c.real_sort(), c.real_sort());
		    
		    func_decl rho_64 = function("rho_64", c.int_sort(), c.int_sort());
		    func_decl rho_primed_64 = function("rho_primed_64", c.real_sort(), c.real_sort());
		    
		    expr pwl_46 = c.int_const("pwl_46");
		    s.add(pwl_46 >= (int)segLower + 1 && pwl_46 <= (int)segUpper);
		    
		    expr pwl_64 = c.int_const("pwl_64");
		    s.add(pwl_64 >= (int)segLower + 1 && pwl_64 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_46(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_46(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_64(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_64(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_46, t_after_46, implies(((t_before_46 < t_after_46) && (t_before_46 >= (int)segLower + 1) && (t_before_46 <= (int)segUpper) && (t_after_46 >= (int)segLower) && (t_after_46 <= (int)segUpper)), ((rho_46(t_before_46) < rho_46(t_after_46)) && (rho_64(t_before_46) < rho_64(t_after_46))))));
			
			//mutual separation constraint
			s.add(forall(pred_4, pred_6, implies(((rho_46(pred_4) == pred_6) && (pred_4 >= (int)segLower + 1) && (pred_4 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_4_x(pred_4)) * (a_6_x(pred_6) - a_4_x(pred_4))) + ((a_6_y(pred_6) - a_4_y(pred_4)) * (a_6_y(pred_6) - a_4_y(pred_4))) + ((a_6_z(pred_6) - a_4_z(pred_4)) * (a_6_z(pred_6) - a_4_z(pred_4))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_46, implies(((pwl_46 >= (int)segLower + 1) && (pwl_46 <= (int)segUpper)), (rho_primed_46(pwl_46) == rho_46(c.int_val(pwl_46)) + ((pwl_46 - c.int_val(pwl_46)) * (rho_46(c.int_val(pwl_46) + 1) - rho_46(c.int_val(pwl_46))))))));
			s.add(forall(pwl_64, implies(((pwl_64 >= (int)segLower + 1) && (pwl_64 <= (int)segUpper)), (rho_primed_64(pwl_64) == rho_64(c.int_val(pwl_64)) + ((pwl_64 - c.int_val(pwl_64)) * (rho_64(c.int_val(pwl_64) + 1) - rho_64(c.int_val(pwl_64))))))));
			
			//inverse re-timing
			s.add(forall(t_46, implies(((t_46 >= (int)segLower) && (t_46 <= (int)segUpper)), (rho_64(rho_46(t_46)) == t_46))));

			// ================ AGENT 4 AND AGENT 6 END ================ //
			
			// =============== AGENT 4 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_47 = c.int_const("t_47");
		    s.add(t_47 >= (int)segLower + 1 && t_47 <= (int)segUpper);
		    
		    expr t_before_47 = c.int_const("t_before_47");
		    expr t_after_47 = c.int_const("t_after_47");
		    s.add(t_before_47 >= (int)segLower + 1 && t_before_47 <= (int)segUpper && t_after_47 >= (int)segLower && t_after_47 <= (int)segUpper);
		    
		    func_decl rho_47 = function("rho_47", c.int_sort(), c.int_sort());
		    func_decl rho_primed_47 = function("rho_primed_47", c.real_sort(), c.real_sort());
		    
		    func_decl rho_74 = function("rho_74", c.int_sort(), c.int_sort());
		    func_decl rho_primed_74 = function("rho_primed_74", c.real_sort(), c.real_sort());
		    
		    expr pwl_47 = c.int_const("pwl_47");
		    s.add(pwl_47 >= (int)segLower + 1 && pwl_47 <= (int)segUpper);
		    
		    expr pwl_74 = c.int_const("pwl_74");
		    s.add(pwl_74 >= (int)segLower + 1 && pwl_74 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_47(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_47(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_74(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_74(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_47, t_after_47, implies(((t_before_47 < t_after_47) && (t_before_47 >= (int)segLower + 1) && (t_before_47 <= (int)segUpper) && (t_after_47 >= (int)segLower) && (t_after_47 <= (int)segUpper)), ((rho_47(t_before_47) < rho_47(t_after_47)) && (rho_74(t_before_47) < rho_74(t_after_47))))));
			
			//mutual separation constraint
			s.add(forall(pred_4, pred_7, implies(((rho_47(pred_4) == pred_7) && (pred_4 >= (int)segLower + 1) && (pred_4 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_4_x(pred_4)) * (a_7_x(pred_7) - a_4_x(pred_4))) + ((a_7_y(pred_7) - a_4_y(pred_4)) * (a_7_y(pred_7) - a_4_y(pred_4))) + ((a_7_z(pred_7) - a_4_z(pred_4)) * (a_7_z(pred_7) - a_4_z(pred_4))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_47, implies(((pwl_47 >= (int)segLower + 1) && (pwl_47 <= (int)segUpper)), (rho_primed_47(pwl_47) == rho_47(c.int_val(pwl_47)) + ((pwl_47 - c.int_val(pwl_47)) * (rho_47(c.int_val(pwl_47) + 1) - rho_47(c.int_val(pwl_47))))))));
			s.add(forall(pwl_74, implies(((pwl_74 >= (int)segLower + 1) && (pwl_74 <= (int)segUpper)), (rho_primed_74(pwl_74) == rho_74(c.int_val(pwl_74)) + ((pwl_74 - c.int_val(pwl_74)) * (rho_74(c.int_val(pwl_74) + 1) - rho_74(c.int_val(pwl_74))))))));
			
			//inverse re-timing
			s.add(forall(t_47, implies(((t_47 >= (int)segLower) && (t_47 <= (int)segUpper)), (rho_74(rho_47(t_47)) == t_47))));

			// ================ AGENT 4 AND AGENT 7 END ================ //
			
			// =============== AGENT 4 AND AGENT 8 START =============== //
			
			//agent pair smt variables
			expr t_48 = c.int_const("t_48");
		    s.add(t_48 >= (int)segLower + 1 && t_48 <= (int)segUpper);
		    
		    expr t_before_48 = c.int_const("t_before_48");
		    expr t_after_48 = c.int_const("t_after_48");
		    s.add(t_before_48 >= (int)segLower + 1 && t_before_48 <= (int)segUpper && t_after_48 >= (int)segLower && t_after_48 <= (int)segUpper);
		    
		    func_decl rho_48 = function("rho_48", c.int_sort(), c.int_sort());
		    func_decl rho_primed_48 = function("rho_primed_48", c.real_sort(), c.real_sort());
		    
		    func_decl rho_84 = function("rho_84", c.int_sort(), c.int_sort());
		    func_decl rho_primed_84 = function("rho_primed_84", c.real_sort(), c.real_sort());
		    
		    expr pwl_48 = c.int_const("pwl_48");
		    s.add(pwl_48 >= (int)segLower + 1 && pwl_48 <= (int)segUpper);
		    
		    expr pwl_84 = c.int_const("pwl_84");
		    s.add(pwl_84 >= (int)segLower + 1 && pwl_84 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_48(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_48(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_84(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_84(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_48, t_after_48, implies(((t_before_48 < t_after_48) && (t_before_48 >= (int)segLower + 1) && (t_before_48 <= (int)segUpper) && (t_after_48 >= (int)segLower) && (t_after_48 <= (int)segUpper)), ((rho_48(t_before_48) < rho_48(t_after_48)) && (rho_84(t_before_48) < rho_84(t_after_48))))));
			
			//mutual separation constraint
			s.add(forall(pred_4, pred_8, implies(((rho_48(pred_4) == pred_8) && (pred_4 >= (int)segLower + 1) && (pred_4 <= (int)segUpper) && (pred_8 >= (int)segLower) && (pred_8 <= (int)segUpper)), (c.real_val(delta) <= (((a_8_x(pred_8) - a_4_x(pred_4)) * (a_8_x(pred_8) - a_4_x(pred_4))) + ((a_8_y(pred_8) - a_4_y(pred_4)) * (a_8_y(pred_8) - a_4_y(pred_4))) + ((a_8_z(pred_8) - a_4_z(pred_4)) * (a_8_z(pred_8) - a_4_z(pred_4))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_48, implies(((pwl_48 >= (int)segLower + 1) && (pwl_48 <= (int)segUpper)), (rho_primed_48(pwl_48) == rho_48(c.int_val(pwl_48)) + ((pwl_48 - c.int_val(pwl_48)) * (rho_48(c.int_val(pwl_48) + 1) - rho_48(c.int_val(pwl_48))))))));
			s.add(forall(pwl_84, implies(((pwl_84 >= (int)segLower + 1) && (pwl_84 <= (int)segUpper)), (rho_primed_84(pwl_84) == rho_84(c.int_val(pwl_84)) + ((pwl_84 - c.int_val(pwl_84)) * (rho_84(c.int_val(pwl_84) + 1) - rho_84(c.int_val(pwl_84))))))));
			
			//inverse re-timing
			s.add(forall(t_48, implies(((t_48 >= (int)segLower) && (t_48 <= (int)segUpper)), (rho_84(rho_48(t_48)) == t_48))));

			// ================ AGENT 4 AND AGENT 8 END ================ //
			
			// =============== AGENT 5 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_56 = c.int_const("t_56");
		    s.add(t_56 >= (int)segLower + 1 && t_56 <= (int)segUpper);
		    
		    expr t_before_56 = c.int_const("t_before_56");
		    expr t_after_56 = c.int_const("t_after_56");
		    s.add(t_before_56 >= (int)segLower + 1 && t_before_56 <= (int)segUpper && t_after_56 >= (int)segLower && t_after_56 <= (int)segUpper);
		    
		    func_decl rho_56 = function("rho_56", c.int_sort(), c.int_sort());
		    func_decl rho_primed_56 = function("rho_primed_56", c.real_sort(), c.real_sort());
		    
		    func_decl rho_65 = function("rho_65", c.int_sort(), c.int_sort());
		    func_decl rho_primed_65 = function("rho_primed_65", c.real_sort(), c.real_sort());
		    
		    expr pwl_56 = c.int_const("pwl_56");
		    s.add(pwl_56 >= (int)segLower + 1 && pwl_56 <= (int)segUpper);
		    
		    expr pwl_65 = c.int_const("pwl_65");
		    s.add(pwl_65 >= (int)segLower + 1 && pwl_65 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_56(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_56(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_65(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_65(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_56, t_after_56, implies(((t_before_56 < t_after_56) && (t_before_56 >= (int)segLower + 1) && (t_before_56 <= (int)segUpper) && (t_after_56 >= (int)segLower) && (t_after_56 <= (int)segUpper)), ((rho_56(t_before_56) < rho_56(t_after_56)) && (rho_65(t_before_56) < rho_65(t_after_56))))));
			
			//mutual separation constraint
			s.add(forall(pred_5, pred_6, implies(((rho_56(pred_5) == pred_6) && (pred_5 >= (int)segLower + 1) && (pred_5 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_5_x(pred_5)) * (a_6_x(pred_6) - a_5_x(pred_5))) + ((a_6_y(pred_6) - a_5_y(pred_5)) * (a_6_y(pred_6) - a_5_y(pred_5))) + ((a_6_z(pred_6) - a_5_z(pred_5)) * (a_6_z(pred_6) - a_5_z(pred_5))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_56, implies(((pwl_56 >= (int)segLower + 1) && (pwl_56 <= (int)segUpper)), (rho_primed_56(pwl_56) == rho_56(c.int_val(pwl_56)) + ((pwl_56 - c.int_val(pwl_56)) * (rho_56(c.int_val(pwl_56) + 1) - rho_56(c.int_val(pwl_56))))))));
			s.add(forall(pwl_65, implies(((pwl_65 >= (int)segLower + 1) && (pwl_65 <= (int)segUpper)), (rho_primed_65(pwl_65) == rho_65(c.int_val(pwl_65)) + ((pwl_65 - c.int_val(pwl_65)) * (rho_65(c.int_val(pwl_65) + 1) - rho_65(c.int_val(pwl_65))))))));
			
			//inverse re-timing
			s.add(forall(t_56, implies(((t_56 >= (int)segLower) && (t_56 <= (int)segUpper)), (rho_65(rho_56(t_56)) == t_56))));

			// ================ AGENT 5 AND AGENT 6 END ================ //
			
			// =============== AGENT 5 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_57 = c.int_const("t_57");
		    s.add(t_57 >= (int)segLower + 1 && t_57 <= (int)segUpper);
		    
		    expr t_before_57 = c.int_const("t_before_57");
		    expr t_after_57 = c.int_const("t_after_57");
		    s.add(t_before_57 >= (int)segLower + 1 && t_before_57 <= (int)segUpper && t_after_57 >= (int)segLower && t_after_57 <= (int)segUpper);
		    
		    func_decl rho_57 = function("rho_57", c.int_sort(), c.int_sort());
		    func_decl rho_primed_57 = function("rho_primed_57", c.real_sort(), c.real_sort());
		    
		    func_decl rho_75 = function("rho_75", c.int_sort(), c.int_sort());
		    func_decl rho_primed_75 = function("rho_primed_75", c.real_sort(), c.real_sort());
		    
		    expr pwl_57 = c.int_const("pwl_57");
		    s.add(pwl_57 >= (int)segLower + 1 && pwl_57 <= (int)segUpper);
		    
		    expr pwl_75 = c.int_const("pwl_75");
		    s.add(pwl_75 >= (int)segLower + 1 && pwl_75 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_57(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_57(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_75(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_75(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_57, t_after_57, implies(((t_before_57 < t_after_57) && (t_before_57 >= (int)segLower + 1) && (t_before_57 <= (int)segUpper) && (t_after_57 >= (int)segLower) && (t_after_57 <= (int)segUpper)), ((rho_57(t_before_57) < rho_57(t_after_57)) && (rho_75(t_before_57) < rho_75(t_after_57))))));
			
			//mutual separation constraint
			s.add(forall(pred_5, pred_7, implies(((rho_57(pred_5) == pred_7) && (pred_5 >= (int)segLower + 1) && (pred_5 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_5_x(pred_5)) * (a_7_x(pred_7) - a_5_x(pred_5))) + ((a_7_y(pred_7) - a_5_y(pred_5)) * (a_7_y(pred_7) - a_5_y(pred_5))) + ((a_7_z(pred_7) - a_5_z(pred_5)) * (a_7_z(pred_7) - a_5_z(pred_5))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_57, implies(((pwl_57 >= (int)segLower + 1) && (pwl_57 <= (int)segUpper)), (rho_primed_57(pwl_57) == rho_57(c.int_val(pwl_57)) + ((pwl_57 - c.int_val(pwl_57)) * (rho_57(c.int_val(pwl_57) + 1) - rho_57(c.int_val(pwl_57))))))));
			s.add(forall(pwl_75, implies(((pwl_75 >= (int)segLower + 1) && (pwl_75 <= (int)segUpper)), (rho_primed_75(pwl_75) == rho_75(c.int_val(pwl_75)) + ((pwl_75 - c.int_val(pwl_75)) * (rho_75(c.int_val(pwl_75) + 1) - rho_75(c.int_val(pwl_75))))))));
			
			//inverse re-timing
			s.add(forall(t_57, implies(((t_57 >= (int)segLower) && (t_57 <= (int)segUpper)), (rho_75(rho_57(t_57)) == t_57))));

			// ================ AGENT 5 AND AGENT 7 END ================ //
			
			// =============== AGENT 5 AND AGENT 8 START =============== //
			
			//agent pair smt variables
			expr t_58 = c.int_const("t_58");
		    s.add(t_58 >= (int)segLower + 1 && t_58 <= (int)segUpper);
		    
		    expr t_before_58 = c.int_const("t_before_58");
		    expr t_after_58 = c.int_const("t_after_58");
		    s.add(t_before_58 >= (int)segLower + 1 && t_before_58 <= (int)segUpper && t_after_58 >= (int)segLower && t_after_58 <= (int)segUpper);
		    
		    func_decl rho_58 = function("rho_58", c.int_sort(), c.int_sort());
		    func_decl rho_primed_58 = function("rho_primed_58", c.real_sort(), c.real_sort());
		    
		    func_decl rho_85 = function("rho_85", c.int_sort(), c.int_sort());
		    func_decl rho_primed_85 = function("rho_primed_85", c.real_sort(), c.real_sort());
		    
		    expr pwl_58 = c.int_const("pwl_58");
		    s.add(pwl_58 >= (int)segLower + 1 && pwl_58 <= (int)segUpper);
		    
		    expr pwl_85 = c.int_const("pwl_85");
		    s.add(pwl_85 >= (int)segLower + 1 && pwl_85 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_58(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_58(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_85(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_85(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_58, t_after_58, implies(((t_before_58 < t_after_58) && (t_before_58 >= (int)segLower + 1) && (t_before_58 <= (int)segUpper) && (t_after_58 >= (int)segLower) && (t_after_58 <= (int)segUpper)), ((rho_58(t_before_58) < rho_58(t_after_58)) && (rho_85(t_before_58) < rho_85(t_after_58))))));
			
			//mutual separation constraint
			s.add(forall(pred_5, pred_8, implies(((rho_58(pred_5) == pred_8) && (pred_5 >= (int)segLower + 1) && (pred_5 <= (int)segUpper) && (pred_8 >= (int)segLower) && (pred_8 <= (int)segUpper)), (c.real_val(delta) <= (((a_8_x(pred_8) - a_5_x(pred_5)) * (a_8_x(pred_8) - a_5_x(pred_5))) + ((a_8_y(pred_8) - a_5_y(pred_5)) * (a_8_y(pred_8) - a_5_y(pred_5))) + ((a_8_z(pred_8) - a_5_z(pred_5)) * (a_8_z(pred_8) - a_5_z(pred_5))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_58, implies(((pwl_58 >= (int)segLower + 1) && (pwl_58 <= (int)segUpper)), (rho_primed_58(pwl_58) == rho_58(c.int_val(pwl_58)) + ((pwl_58 - c.int_val(pwl_58)) * (rho_58(c.int_val(pwl_58) + 1) - rho_58(c.int_val(pwl_58))))))));
			s.add(forall(pwl_85, implies(((pwl_85 >= (int)segLower + 1) && (pwl_85 <= (int)segUpper)), (rho_primed_85(pwl_85) == rho_85(c.int_val(pwl_85)) + ((pwl_85 - c.int_val(pwl_85)) * (rho_85(c.int_val(pwl_85) + 1) - rho_85(c.int_val(pwl_85))))))));
			
			//inverse re-timing
			s.add(forall(t_58, implies(((t_58 >= (int)segLower) && (t_58 <= (int)segUpper)), (rho_85(rho_58(t_58)) == t_58))));

			// ================ AGENT 5 AND AGENT 8 END ================ //
			
			// =============== AGENT 6 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_67 = c.int_const("t_67");
		    s.add(t_67 >= (int)segLower + 1 && t_67 <= (int)segUpper);
		    
		    expr t_before_67 = c.int_const("t_before_67");
		    expr t_after_67 = c.int_const("t_after_67");
		    s.add(t_before_67 >= (int)segLower + 1 && t_before_67 <= (int)segUpper && t_after_67 >= (int)segLower && t_after_67 <= (int)segUpper);
		    
		    func_decl rho_67 = function("rho_67", c.int_sort(), c.int_sort());
		    func_decl rho_primed_67 = function("rho_primed_67", c.real_sort(), c.real_sort());
		    
		    func_decl rho_76 = function("rho_76", c.int_sort(), c.int_sort());
		    func_decl rho_primed_76 = function("rho_primed_76", c.real_sort(), c.real_sort());
		    
		    expr pwl_67 = c.int_const("pwl_67");
		    s.add(pwl_67 >= (int)segLower + 1 && pwl_67 <= (int)segUpper);
		    
		    expr pwl_76 = c.int_const("pwl_76");
		    s.add(pwl_76 >= (int)segLower + 1 && pwl_76 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_67(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_67(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_76(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_76(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_67, t_after_67, implies(((t_before_67 < t_after_67) && (t_before_67 >= (int)segLower + 1) && (t_before_67 <= (int)segUpper) && (t_after_67 >= (int)segLower) && (t_after_67 <= (int)segUpper)), ((rho_67(t_before_67) < rho_67(t_after_67)) && (rho_76(t_before_67) < rho_76(t_after_67))))));
			
			//mutual separation constraint
			s.add(forall(pred_6, pred_7, implies(((rho_67(pred_6) == pred_7) && (pred_6 >= (int)segLower + 1) && (pred_6 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_6_x(pred_6)) * (a_7_x(pred_7) - a_6_x(pred_6))) + ((a_7_y(pred_7) - a_6_y(pred_6)) * (a_7_y(pred_7) - a_6_y(pred_6))) + ((a_7_z(pred_7) - a_6_z(pred_6)) * (a_7_z(pred_7) - a_6_z(pred_6))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_67, implies(((pwl_67 >= (int)segLower + 1) && (pwl_67 <= (int)segUpper)), (rho_primed_67(pwl_67) == rho_67(c.int_val(pwl_67)) + ((pwl_67 - c.int_val(pwl_67)) * (rho_67(c.int_val(pwl_67) + 1) - rho_67(c.int_val(pwl_67))))))));
			s.add(forall(pwl_76, implies(((pwl_76 >= (int)segLower + 1) && (pwl_76 <= (int)segUpper)), (rho_primed_76(pwl_76) == rho_76(c.int_val(pwl_76)) + ((pwl_76 - c.int_val(pwl_76)) * (rho_76(c.int_val(pwl_76) + 1) - rho_76(c.int_val(pwl_76))))))));
			
			//inverse re-timing
			s.add(forall(t_67, implies(((t_67 >= (int)segLower) && (t_67 <= (int)segUpper)), (rho_76(rho_67(t_67)) == t_67))));

			// ================ AGENT 6 AND AGENT 7 END ================ //
			
			// =============== AGENT 6 AND AGENT 8 START =============== //
			
			//agent pair smt variables
			expr t_68 = c.int_const("t_68");
		    s.add(t_68 >= (int)segLower + 1 && t_68 <= (int)segUpper);
		    
		    expr t_before_68 = c.int_const("t_before_68");
		    expr t_after_68 = c.int_const("t_after_68");
		    s.add(t_before_68 >= (int)segLower + 1 && t_before_68 <= (int)segUpper && t_after_68 >= (int)segLower && t_after_68 <= (int)segUpper);
		    
		    func_decl rho_68 = function("rho_68", c.int_sort(), c.int_sort());
		    func_decl rho_primed_68 = function("rho_primed_68", c.real_sort(), c.real_sort());
		    
		    func_decl rho_86 = function("rho_86", c.int_sort(), c.int_sort());
		    func_decl rho_primed_86 = function("rho_primed_86", c.real_sort(), c.real_sort());
		    
		    expr pwl_68 = c.int_const("pwl_68");
		    s.add(pwl_68 >= (int)segLower + 1 && pwl_68 <= (int)segUpper);
		    
		    expr pwl_86 = c.int_const("pwl_86");
		    s.add(pwl_86 >= (int)segLower + 1 && pwl_86 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_68(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_68(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_86(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_86(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_68, t_after_68, implies(((t_before_68 < t_after_68) && (t_before_68 >= (int)segLower + 1) && (t_before_68 <= (int)segUpper) && (t_after_68 >= (int)segLower) && (t_after_68 <= (int)segUpper)), ((rho_68(t_before_68) < rho_68(t_after_68)) && (rho_86(t_before_68) < rho_86(t_after_68))))));
			
			//mutual separation constraint
			s.add(forall(pred_6, pred_8, implies(((rho_68(pred_6) == pred_8) && (pred_6 >= (int)segLower + 1) && (pred_6 <= (int)segUpper) && (pred_8 >= (int)segLower) && (pred_8 <= (int)segUpper)), (c.real_val(delta) <= (((a_8_x(pred_8) - a_6_x(pred_6)) * (a_8_x(pred_8) - a_6_x(pred_6))) + ((a_8_y(pred_8) - a_6_y(pred_6)) * (a_8_y(pred_8) - a_6_y(pred_6))) + ((a_8_z(pred_8) - a_6_z(pred_6)) * (a_8_z(pred_8) - a_6_z(pred_6))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_68, implies(((pwl_68 >= (int)segLower + 1) && (pwl_68 <= (int)segUpper)), (rho_primed_68(pwl_68) == rho_68(c.int_val(pwl_68)) + ((pwl_68 - c.int_val(pwl_68)) * (rho_68(c.int_val(pwl_68) + 1) - rho_68(c.int_val(pwl_68))))))));
			s.add(forall(pwl_86, implies(((pwl_86 >= (int)segLower + 1) && (pwl_86 <= (int)segUpper)), (rho_primed_86(pwl_86) == rho_86(c.int_val(pwl_86)) + ((pwl_86 - c.int_val(pwl_86)) * (rho_86(c.int_val(pwl_86) + 1) - rho_86(c.int_val(pwl_86))))))));
			
			//inverse re-timing
			s.add(forall(t_68, implies(((t_68 >= (int)segLower) && (t_68 <= (int)segUpper)), (rho_86(rho_68(t_68)) == t_68))));

			// ================ AGENT 6 AND AGENT 8 END ================ //
			
			// =============== AGENT 7 AND AGENT 8 START =============== //
			
			//agent pair smt variables
			expr t_78 = c.int_const("t_78");
		    s.add(t_78 >= (int)segLower + 1 && t_78 <= (int)segUpper);
		    
		    expr t_before_78 = c.int_const("t_before_78");
		    expr t_after_78 = c.int_const("t_after_78");
		    s.add(t_before_78 >= (int)segLower + 1 && t_before_78 <= (int)segUpper && t_after_78 >= (int)segLower && t_after_78 <= (int)segUpper);
		    
		    func_decl rho_78 = function("rho_78", c.int_sort(), c.int_sort());
		    func_decl rho_primed_78 = function("rho_primed_78", c.real_sort(), c.real_sort());
		    
		    func_decl rho_87 = function("rho_87", c.int_sort(), c.int_sort());
		    func_decl rho_primed_87 = function("rho_primed_87", c.real_sort(), c.real_sort());
		    
		    expr pwl_78 = c.int_const("pwl_78");
		    s.add(pwl_78 >= (int)segLower + 1 && pwl_78 <= (int)segUpper);
		    
		    expr pwl_87 = c.int_const("pwl_87");
		    s.add(pwl_87 >= (int)segLower + 1 && pwl_87 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_78(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_78(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_87(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_87(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_78, t_after_78, implies(((t_before_78 < t_after_78) && (t_before_78 >= (int)segLower + 1) && (t_before_78 <= (int)segUpper) && (t_after_78 >= (int)segLower) && (t_after_78 <= (int)segUpper)), ((rho_78(t_before_78) < rho_78(t_after_78)) && (rho_87(t_before_78) < rho_87(t_after_78))))));
			
			//mutual separation constraint
			s.add(forall(pred_7, pred_8, implies(((rho_78(pred_7) == pred_8) && (pred_7 >= (int)segLower + 1) && (pred_7 <= (int)segUpper) && (pred_8 >= (int)segLower) && (pred_8 <= (int)segUpper)), (c.real_val(delta) <= (((a_8_x(pred_8) - a_7_x(pred_7)) * (a_8_x(pred_8) - a_7_x(pred_7))) + ((a_8_y(pred_8) - a_7_y(pred_7)) * (a_8_y(pred_8) - a_7_y(pred_7))) + ((a_8_z(pred_8) - a_7_z(pred_7)) * (a_8_z(pred_8) - a_7_z(pred_7))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_78, implies(((pwl_78 >= (int)segLower + 1) && (pwl_78 <= (int)segUpper)), (rho_primed_78(pwl_78) == rho_78(c.int_val(pwl_78)) + ((pwl_78 - c.int_val(pwl_78)) * (rho_78(c.int_val(pwl_78) + 1) - rho_78(c.int_val(pwl_78))))))));
			s.add(forall(pwl_87, implies(((pwl_87 >= (int)segLower + 1) && (pwl_87 <= (int)segUpper)), (rho_primed_87(pwl_87) == rho_87(c.int_val(pwl_87)) + ((pwl_87 - c.int_val(pwl_87)) * (rho_87(c.int_val(pwl_87) + 1) - rho_87(c.int_val(pwl_87))))))));
			
			//inverse re-timing
			s.add(forall(t_78, implies(((t_78 >= (int)segLower) && (t_78 <= (int)segUpper)), (rho_87(rho_78(t_78)) == t_78))));

			// ================ AGENT 7 AND AGENT 8 END ================ //
			
			if(s.check() == sat)
		    {
		    	std::string verdict = std::to_string(i) + " : Sat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    else
		    {
		    	std::string verdict = std::to_string(i) + " : Unsat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    
		    //reset solver
		    //s.reset();
		    
		    //build and show model
		    //model m = s.get_model();
    		//std::cout << m << "\n";
	    }
	}
	//return verdicts;
}

void runSolver_10(double eps, int segCount, double sigDur, int msgLim)
{
	//enable parallel mode
	//set_param("parallel.enable", true);
	
	//get data
	std::vector<std::vector<std::string>> agentData_0 = getData("agent_0.txt");
	std::vector<std::vector<std::string>> agentData_1 = getData("agent_1.txt");
	std::vector<std::vector<std::string>> agentData_2 = getData("agent_2.txt");
	std::vector<std::vector<std::string>> agentData_3 = getData("agent_3.txt");
	std::vector<std::vector<std::string>> agentData_4 = getData("agent_4.txt");
	std::vector<std::vector<std::string>> agentData_5 = getData("agent_5.txt");
	std::vector<std::vector<std::string>> agentData_6 = getData("agent_6.txt");
	std::vector<std::vector<std::string>> agentData_7 = getData("agent_7.txt");
	std::vector<std::vector<std::string>> agentData_8 = getData("agent_8.txt");
	std::vector<std::vector<std::string>> agentData_9 = getData("agent_9.txt");
	
	//safety checks
	if(!(std::stod(agentData_0[0][0]) == 0 && std::stod(agentData_1[0][0]) == 0))
	{
		return;
	}
	
	if(std::stod(agentData_0[1][0]) != std::stod(agentData_1[1][0]))
	{
		return;
	}
	
	//second time-stamp on agent that is to be re-timed
	double t1 = std::stod(agentData_0[1][0]);
	
	//delta
	int delta = 0;
	
	//segment duration
	double segDur = sigDur / segCount;
	
	//check if the segment duration is smaller than the sampling period
	if(segDur < t1)
	{
		segCount = sigDur / t1;
	}
	
	//multiplier for normalization
	double mult = 1 / t1;
	
	//normalization of paramters
	eps *= mult;
	sigDur *= mult;
	segDur *= mult;
	
	//verdict vector
	std::vector<std::string> verdicts;
	
	#pragma omp parallel
	{
		#pragma omp for
		for(int i = 0; i < segCount; i++) 
	    {			
			//segment bounds
			double segLower = (i * segDur) - eps;
			double segUpper = (i + 1) * segDur;
			
		    context c;

		    //solver
		    solver s(c);
		    
		    //co-ord functions
		    func_decl a_0_x = function("a_0_x", c.int_sort(), c.real_sort());
		    func_decl a_0_y = function("a_0_y", c.int_sort(), c.real_sort());
		    func_decl a_0_z = function("a_0_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_1_x = function("a_1_x", c.int_sort(), c.real_sort());
		    func_decl a_1_y = function("a_1_y", c.int_sort(), c.real_sort());
		    func_decl a_1_z = function("a_1_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_2_x = function("a_2_x", c.int_sort(), c.real_sort());
		    func_decl a_2_y = function("a_2_y", c.int_sort(), c.real_sort());
		    func_decl a_2_z = function("a_2_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_3_x = function("a_3_x", c.int_sort(), c.real_sort());
		    func_decl a_3_y = function("a_3_y", c.int_sort(), c.real_sort());
		    func_decl a_3_z = function("a_3_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_4_x = function("a_4_x", c.int_sort(), c.real_sort());
		    func_decl a_4_y = function("a_4_y", c.int_sort(), c.real_sort());
		    func_decl a_4_z = function("a_4_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_5_x = function("a_5_x", c.int_sort(), c.real_sort());
		    func_decl a_5_y = function("a_5_y", c.int_sort(), c.real_sort());
		    func_decl a_5_z = function("a_5_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_6_x = function("a_6_x", c.int_sort(), c.real_sort());
		    func_decl a_6_y = function("a_6_y", c.int_sort(), c.real_sort());
		    func_decl a_6_z = function("a_6_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_7_x = function("a_7_x", c.int_sort(), c.real_sort());
		    func_decl a_7_y = function("a_7_y", c.int_sort(), c.real_sort());
		    func_decl a_7_z = function("a_7_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_8_x = function("a_8_x", c.int_sort(), c.real_sort());
		    func_decl a_8_y = function("a_8_y", c.int_sort(), c.real_sort());
		    func_decl a_8_z = function("a_8_z", c.int_sort(), c.real_sort());
		    
		    func_decl a_9_x = function("a_9_x", c.int_sort(), c.real_sort());
		    func_decl a_9_y = function("a_9_y", c.int_sort(), c.real_sort());
		    func_decl a_9_z = function("a_9_z", c.int_sort(), c.real_sort());
		    
		    //populate co-ord functions
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_0.size())
		        {
		        	s.add(a_0_x(j) == c.real_val(agentData_0[j][1].c_str()));
		        	s.add(a_0_y(j) == c.real_val(agentData_0[j][2].c_str()));
		        	s.add(a_0_z(j) == c.real_val(agentData_0[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_1.size())
		        {
		        	s.add(a_1_x(j) == c.real_val(agentData_1[j][1].c_str()));
		        	s.add(a_1_y(j) == c.real_val(agentData_1[j][2].c_str()));
		        	s.add(a_1_z(j) == c.real_val(agentData_1[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_2.size())
		        {
		        	s.add(a_2_x(j) == c.real_val(agentData_2[j][1].c_str()));
		        	s.add(a_2_y(j) == c.real_val(agentData_2[j][2].c_str()));
		        	s.add(a_2_z(j) == c.real_val(agentData_2[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_3.size())
		        {
		        	s.add(a_3_x(j) == c.real_val(agentData_3[j][1].c_str()));
		        	s.add(a_3_y(j) == c.real_val(agentData_3[j][2].c_str()));
		        	s.add(a_3_z(j) == c.real_val(agentData_3[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_4.size())
		        {
		        	s.add(a_4_x(j) == c.real_val(agentData_4[j][1].c_str()));
		        	s.add(a_4_y(j) == c.real_val(agentData_4[j][2].c_str()));
		        	s.add(a_4_z(j) == c.real_val(agentData_4[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_5.size())
		        {
		        	s.add(a_5_x(j) == c.real_val(agentData_5[j][1].c_str()));
		        	s.add(a_5_y(j) == c.real_val(agentData_5[j][2].c_str()));
		        	s.add(a_5_z(j) == c.real_val(agentData_5[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_6.size())
		        {
		        	s.add(a_6_x(j) == c.real_val(agentData_6[j][1].c_str()));
		        	s.add(a_6_y(j) == c.real_val(agentData_6[j][2].c_str()));
		        	s.add(a_6_z(j) == c.real_val(agentData_6[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_7.size())
		        {
		        	s.add(a_7_x(j) == c.real_val(agentData_7[j][1].c_str()));
		        	s.add(a_7_y(j) == c.real_val(agentData_7[j][2].c_str()));
		        	s.add(a_7_z(j) == c.real_val(agentData_7[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_8.size())
		        {
		        	s.add(a_8_x(j) == c.real_val(agentData_8[j][1].c_str()));
		        	s.add(a_8_y(j) == c.real_val(agentData_8[j][2].c_str()));
		        	s.add(a_8_z(j) == c.real_val(agentData_8[j][3].c_str()));
				}
		    }
		    
		    for(int j = segLower + 1; j <= segUpper; j++)
		    {
		        if(j >= 0 && j < agentData_9.size())
		        {
		        	s.add(a_9_x(j) == c.real_val(agentData_9[j][1].c_str()));
		        	s.add(a_9_y(j) == c.real_val(agentData_9[j][2].c_str()));
		        	s.add(a_9_z(j) == c.real_val(agentData_9[j][3].c_str()));
				}
		    }
		    
		    //general smt variables		  
			expr pred_0 = c.int_const("pred_0");
			s.add(pred_0 >= (int)segLower + 1 && pred_0 <= (int)segUpper);
			
		    expr pred_1 = c.int_const("pred_1");
		    s.add(pred_1 >= (int)segLower + 1 && pred_1 <= (int)segUpper);
		    
		    expr pred_2 = c.int_const("pred_2");
		    s.add(pred_2 >= (int)segLower + 1 && pred_2 <= (int)segUpper);
		    
		    expr pred_3 = c.int_const("pred_3");
		    s.add(pred_3 >= (int)segLower + 1 && pred_3 <= (int)segUpper);
		    
		    expr pred_4 = c.int_const("pred_4");
		    s.add(pred_4 >= (int)segLower + 1 && pred_4 <= (int)segUpper);
		    
		    expr pred_5 = c.int_const("pred_5");
		    s.add(pred_5 >= (int)segLower + 1 && pred_5 <= (int)segUpper);
		    
		    expr pred_6 = c.int_const("pred_6");
		    s.add(pred_6 >= (int)segLower + 1 && pred_6 <= (int)segUpper);
		    
		    expr pred_7 = c.int_const("pred_7");
		    s.add(pred_7 >= (int)segLower + 1 && pred_7 <= (int)segUpper);
		    
		    expr pred_8 = c.int_const("pred_8");
		    s.add(pred_8 >= (int)segLower + 1 && pred_8 <= (int)segUpper);
		    
		    expr pred_9 = c.int_const("pred_9");
		    s.add(pred_9 >= (int)segLower + 1 && pred_9 <= (int)segUpper);
		    
		    // =============== AGENT 0 AND AGENT 1 START =============== //
			
			//agent pair smt variables
			expr t_01 = c.int_const("t_01");
		    s.add(t_01 >= (int)segLower + 1 && t_01 <= (int)segUpper);
		    
		    expr t_before_01 = c.int_const("t_before_01");
		    expr t_after_01 = c.int_const("t_after_01");
		    s.add(t_before_01 >= (int)segLower + 1 && t_before_01 <= (int)segUpper && t_after_01 >= (int)segLower && t_after_01 <= (int)segUpper);
		    
		    func_decl rho_01 = function("rho_01", c.int_sort(), c.int_sort());
		    func_decl rho_primed_01 = function("rho_primed_01", c.real_sort(), c.real_sort());
		    
		    func_decl rho_10 = function("rho_10", c.int_sort(), c.int_sort());
		    func_decl rho_primed_10 = function("rho_primed_10", c.real_sort(), c.real_sort());
		    
		    expr pwl_01 = c.int_const("pwl_01");
		    s.add(pwl_01 >= (int)segLower + 1 && pwl_01 <= (int)segUpper);
		    
		    expr pwl_10 = c.int_const("pwl_10");
		    s.add(pwl_10 >= (int)segLower + 1 && pwl_10 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_01(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_10(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_01, t_after_01, implies(((t_before_01 < t_after_01) && (t_before_01 >= (int)segLower + 1) && (t_before_01 <= (int)segUpper) && (t_after_01 >= (int)segLower) && (t_after_01 <= (int)segUpper)), ((rho_01(t_before_01) < rho_01(t_after_01)) && (rho_10(t_before_01) < rho_10(t_after_01))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_1, implies(((rho_01(pred_0) == pred_1) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_1 >= (int)segLower) && (pred_1 <= (int)segUpper)), (c.real_val(delta) <= (((a_1_x(pred_1) - a_0_x(pred_0)) * (a_1_x(pred_1) - a_0_x(pred_0))) + ((a_1_y(pred_1) - a_0_y(pred_0)) * (a_1_y(pred_1) - a_0_y(pred_0))) + ((a_1_z(pred_1) - a_0_z(pred_0)) * (a_1_z(pred_1) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_01, implies(((pwl_01 >= (int)segLower + 1) && (pwl_01 <= (int)segUpper)), (rho_primed_01(pwl_01) == rho_01(c.int_val(pwl_01)) + ((pwl_01 - c.int_val(pwl_01)) * (rho_01(c.int_val(pwl_01) + 1) - rho_01(c.int_val(pwl_01))))))));
			s.add(forall(pwl_10, implies(((pwl_10 >= (int)segLower + 1) && (pwl_10 <= (int)segUpper)), (rho_primed_10(pwl_10) == rho_10(c.int_val(pwl_10)) + ((pwl_10 - c.int_val(pwl_10)) * (rho_10(c.int_val(pwl_10) + 1) - rho_10(c.int_val(pwl_10))))))));
			
			//inverse re-timing
			s.add(forall(t_01, implies(((t_01 >= (int)segLower) && (t_01 <= (int)segUpper)), (rho_10(rho_01(t_01)) == t_01))));

			// ================ AGENT 0 AND AGENT 1 END ================ //
			
			// =============== AGENT 0 AND AGENT 2 START =============== //
			
			//agent pair smt variables
			expr t_02 = c.int_const("t_02");
		    s.add(t_02 >= (int)segLower + 1 && t_02 <= (int)segUpper);
		    
		    expr t_before_02 = c.int_const("t_before_02");
		    expr t_after_02 = c.int_const("t_after_02");
		    s.add(t_before_02 >= (int)segLower + 1 && t_before_02 <= (int)segUpper && t_after_02 >= (int)segLower && t_after_02 <= (int)segUpper);
		    
		    func_decl rho_02 = function("rho_02", c.int_sort(), c.int_sort());
		    func_decl rho_primed_02 = function("rho_primed_02", c.real_sort(), c.real_sort());
		    
		    func_decl rho_20 = function("rho_20", c.int_sort(), c.int_sort());
		    func_decl rho_primed_20 = function("rho_primed_20", c.real_sort(), c.real_sort());
		    
		    expr pwl_02 = c.int_const("pwl_02");
		    s.add(pwl_02 >= (int)segLower + 1 && pwl_02 <= (int)segUpper);
		    
		    expr pwl_20 = c.int_const("pwl_20");
		    s.add(pwl_20 >= (int)segLower + 1 && pwl_20 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_02(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_02(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_20(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_20(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_02, t_after_02, implies(((t_before_02 < t_after_02) && (t_before_02 >= (int)segLower + 1) && (t_before_02 <= (int)segUpper) && (t_after_02 >= (int)segLower) && (t_after_02 <= (int)segUpper)), ((rho_02(t_before_02) < rho_02(t_after_02)) && (rho_20(t_before_02) < rho_20(t_after_02))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_2, implies(((rho_02(pred_0) == pred_2) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_2 >= (int)segLower) && (pred_2 <= (int)segUpper)), (c.real_val(delta) <= (((a_2_x(pred_2) - a_0_x(pred_0)) * (a_2_x(pred_2) - a_0_x(pred_0))) + ((a_2_y(pred_2) - a_0_y(pred_0)) * (a_2_y(pred_2) - a_0_y(pred_0))) + ((a_2_z(pred_2) - a_0_z(pred_0)) * (a_2_z(pred_2) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_02, implies(((pwl_02 >= (int)segLower + 1) && (pwl_02 <= (int)segUpper)), (rho_primed_02(pwl_02) == rho_02(c.int_val(pwl_02)) + ((pwl_02 - c.int_val(pwl_02)) * (rho_02(c.int_val(pwl_02) + 1) - rho_02(c.int_val(pwl_02))))))));
			s.add(forall(pwl_20, implies(((pwl_20 >= (int)segLower + 1) && (pwl_20 <= (int)segUpper)), (rho_primed_20(pwl_20) == rho_20(c.int_val(pwl_20)) + ((pwl_20 - c.int_val(pwl_20)) * (rho_20(c.int_val(pwl_20) + 1) - rho_20(c.int_val(pwl_20))))))));
			
			//inverse re-timing
			s.add(forall(t_02, implies(((t_02 >= (int)segLower) && (t_02 <= (int)segUpper)), (rho_20(rho_02(t_02)) == t_02))));

			// ================ AGENT 0 AND AGENT 2 END ================ //
			
			// =============== AGENT 0 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_03 = c.int_const("t_03");
		    s.add(t_03 >= (int)segLower + 1 && t_03 <= (int)segUpper);
		    
		    expr t_before_03 = c.int_const("t_before_03");
		    expr t_after_03 = c.int_const("t_after_03");
		    s.add(t_before_03 >= (int)segLower + 1 && t_before_03 <= (int)segUpper && t_after_03 >= (int)segLower && t_after_03 <= (int)segUpper);
		    
		    func_decl rho_03 = function("rho_03", c.int_sort(), c.int_sort());
		    func_decl rho_primed_03 = function("rho_primed_03", c.real_sort(), c.real_sort());
		    
		    func_decl rho_30 = function("rho_30", c.int_sort(), c.int_sort());
		    func_decl rho_primed_30 = function("rho_primed_30", c.real_sort(), c.real_sort());
		    
		    expr pwl_03 = c.int_const("pwl_03");
		    s.add(pwl_03 >= (int)segLower + 1 && pwl_03 <= (int)segUpper);
		    
		    expr pwl_30 = c.int_const("pwl_30");
		    s.add(pwl_30 >= (int)segLower + 1 && pwl_30 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_03(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_03(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_30(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_30(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_03, t_after_03, implies(((t_before_03 < t_after_03) && (t_before_03 >= (int)segLower + 1) && (t_before_03 <= (int)segUpper) && (t_after_03 >= (int)segLower) && (t_after_03 <= (int)segUpper)), ((rho_03(t_before_03) < rho_03(t_after_03)) && (rho_30(t_before_03) < rho_30(t_after_03))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_3, implies(((rho_03(pred_0) == pred_3) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_0_x(pred_0)) * (a_3_x(pred_3) - a_0_x(pred_0))) + ((a_3_y(pred_3) - a_0_y(pred_0)) * (a_3_y(pred_3) - a_0_y(pred_0))) + ((a_3_z(pred_3) - a_0_z(pred_0)) * (a_3_z(pred_3) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_03, implies(((pwl_03 >= (int)segLower + 1) && (pwl_03 <= (int)segUpper)), (rho_primed_03(pwl_03) == rho_03(c.int_val(pwl_03)) + ((pwl_03 - c.int_val(pwl_03)) * (rho_03(c.int_val(pwl_03) + 1) - rho_03(c.int_val(pwl_03))))))));
			s.add(forall(pwl_30, implies(((pwl_30 >= (int)segLower + 1) && (pwl_30 <= (int)segUpper)), (rho_primed_30(pwl_30) == rho_30(c.int_val(pwl_30)) + ((pwl_30 - c.int_val(pwl_30)) * (rho_30(c.int_val(pwl_30) + 1) - rho_30(c.int_val(pwl_30))))))));
			
			//inverse re-timing
			s.add(forall(t_03, implies(((t_03 >= (int)segLower) && (t_03 <= (int)segUpper)), (rho_30(rho_03(t_03)) == t_03))));

			// ================ AGENT 0 AND AGENT 3 END ================ //
			
			// =============== AGENT 0 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_04 = c.int_const("t_04");
		    s.add(t_04 >= (int)segLower + 1 && t_04 <= (int)segUpper);
		    
		    expr t_before_04 = c.int_const("t_before_04");
		    expr t_after_04 = c.int_const("t_after_04");
		    s.add(t_before_04 >= (int)segLower + 1 && t_before_04 <= (int)segUpper && t_after_04 >= (int)segLower && t_after_04 <= (int)segUpper);
		    
		    func_decl rho_04 = function("rho_04", c.int_sort(), c.int_sort());
		    func_decl rho_primed_04 = function("rho_primed_04", c.real_sort(), c.real_sort());
		    
		    func_decl rho_40 = function("rho_40", c.int_sort(), c.int_sort());
		    func_decl rho_primed_40 = function("rho_primed_40", c.real_sort(), c.real_sort());
		    
		    expr pwl_04 = c.int_const("pwl_04");
		    s.add(pwl_04 >= (int)segLower + 1 && pwl_04 <= (int)segUpper);
		    
		    expr pwl_40 = c.int_const("pwl_40");
		    s.add(pwl_40 >= (int)segLower + 1 && pwl_40 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_04(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_04(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_40(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_40(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_04, t_after_04, implies(((t_before_04 < t_after_04) && (t_before_04 >= (int)segLower + 1) && (t_before_04 <= (int)segUpper) && (t_after_04 >= (int)segLower) && (t_after_04 <= (int)segUpper)), ((rho_04(t_before_04) < rho_04(t_after_04)) && (rho_40(t_before_04) < rho_40(t_after_04))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_4, implies(((rho_04(pred_0) == pred_4) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_0_x(pred_0)) * (a_4_x(pred_4) - a_0_x(pred_0))) + ((a_4_y(pred_4) - a_0_y(pred_0)) * (a_4_y(pred_4) - a_0_y(pred_0))) + ((a_4_z(pred_4) - a_0_z(pred_0)) * (a_4_z(pred_4) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_04, implies(((pwl_04 >= (int)segLower + 1) && (pwl_04 <= (int)segUpper)), (rho_primed_04(pwl_04) == rho_04(c.int_val(pwl_04)) + ((pwl_04 - c.int_val(pwl_04)) * (rho_04(c.int_val(pwl_04) + 1) - rho_04(c.int_val(pwl_04))))))));
			s.add(forall(pwl_40, implies(((pwl_40 >= (int)segLower + 1) && (pwl_40 <= (int)segUpper)), (rho_primed_40(pwl_40) == rho_40(c.int_val(pwl_40)) + ((pwl_40 - c.int_val(pwl_40)) * (rho_40(c.int_val(pwl_40) + 1) - rho_40(c.int_val(pwl_40))))))));
			
			//inverse re-timing
			s.add(forall(t_04, implies(((t_04 >= (int)segLower) && (t_04 <= (int)segUpper)), (rho_40(rho_04(t_04)) == t_04))));

			// ================ AGENT 0 AND AGENT 4 END ================ //
			
			// =============== AGENT 0 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_05 = c.int_const("t_05");
		    s.add(t_05 >= (int)segLower + 1 && t_05 <= (int)segUpper);
		    
		    expr t_before_05 = c.int_const("t_before_05");
		    expr t_after_05 = c.int_const("t_after_05");
		    s.add(t_before_05 >= (int)segLower + 1 && t_before_05 <= (int)segUpper && t_after_05 >= (int)segLower && t_after_05 <= (int)segUpper);
		    
		    func_decl rho_05 = function("rho_05", c.int_sort(), c.int_sort());
		    func_decl rho_primed_05 = function("rho_primed_05", c.real_sort(), c.real_sort());
		    
		    func_decl rho_50 = function("rho_50", c.int_sort(), c.int_sort());
		    func_decl rho_primed_50 = function("rho_primed_50", c.real_sort(), c.real_sort());
		    
		    expr pwl_05 = c.int_const("pwl_05");
		    s.add(pwl_05 >= (int)segLower + 1 && pwl_05 <= (int)segUpper);
		    
		    expr pwl_50 = c.int_const("pwl_50");
		    s.add(pwl_50 >= (int)segLower + 1 && pwl_50 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_05(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_05(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_50(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_50(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_05, t_after_05, implies(((t_before_05 < t_after_05) && (t_before_05 >= (int)segLower + 1) && (t_before_05 <= (int)segUpper) && (t_after_05 >= (int)segLower) && (t_after_05 <= (int)segUpper)), ((rho_05(t_before_05) < rho_05(t_after_05)) && (rho_50(t_before_05) < rho_50(t_after_05))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_5, implies(((rho_05(pred_0) == pred_5) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_0_x(pred_0)) * (a_5_x(pred_5) - a_0_x(pred_0))) + ((a_5_y(pred_5) - a_0_y(pred_0)) * (a_5_y(pred_5) - a_0_y(pred_0))) + ((a_5_z(pred_5) - a_0_z(pred_0)) * (a_5_z(pred_5) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_05, implies(((pwl_05 >= (int)segLower + 1) && (pwl_05 <= (int)segUpper)), (rho_primed_05(pwl_05) == rho_05(c.int_val(pwl_05)) + ((pwl_05 - c.int_val(pwl_05)) * (rho_05(c.int_val(pwl_05) + 1) - rho_05(c.int_val(pwl_05))))))));
			s.add(forall(pwl_50, implies(((pwl_50 >= (int)segLower + 1) && (pwl_50 <= (int)segUpper)), (rho_primed_50(pwl_50) == rho_50(c.int_val(pwl_50)) + ((pwl_50 - c.int_val(pwl_50)) * (rho_50(c.int_val(pwl_50) + 1) - rho_50(c.int_val(pwl_50))))))));
			
			//inverse re-timing
			s.add(forall(t_05, implies(((t_05 >= (int)segLower) && (t_05 <= (int)segUpper)), (rho_50(rho_05(t_05)) == t_05))));

			// ================ AGENT 0 AND AGENT 5 END ================ //
			
			// =============== AGENT 0 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_06 = c.int_const("t_06");
		    s.add(t_06 >= (int)segLower + 1 && t_06 <= (int)segUpper);
		    
		    expr t_before_06 = c.int_const("t_before_06");
		    expr t_after_06 = c.int_const("t_after_06");
		    s.add(t_before_06 >= (int)segLower + 1 && t_before_06 <= (int)segUpper && t_after_06 >= (int)segLower && t_after_06 <= (int)segUpper);
		    
		    func_decl rho_06 = function("rho_06", c.int_sort(), c.int_sort());
		    func_decl rho_primed_06 = function("rho_primed_06", c.real_sort(), c.real_sort());
		    
		    func_decl rho_60 = function("rho_60", c.int_sort(), c.int_sort());
		    func_decl rho_primed_60 = function("rho_primed_60", c.real_sort(), c.real_sort());
		    
		    expr pwl_06 = c.int_const("pwl_06");
		    s.add(pwl_06 >= (int)segLower + 1 && pwl_06 <= (int)segUpper);
		    
		    expr pwl_60 = c.int_const("pwl_60");
		    s.add(pwl_60 >= (int)segLower + 1 && pwl_60 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_06(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_06(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_60(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_60(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_06, t_after_06, implies(((t_before_06 < t_after_06) && (t_before_06 >= (int)segLower + 1) && (t_before_06 <= (int)segUpper) && (t_after_06 >= (int)segLower) && (t_after_06 <= (int)segUpper)), ((rho_06(t_before_06) < rho_06(t_after_06)) && (rho_60(t_before_06) < rho_60(t_after_06))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_6, implies(((rho_06(pred_0) == pred_6) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_0_x(pred_0)) * (a_6_x(pred_6) - a_0_x(pred_0))) + ((a_6_y(pred_6) - a_0_y(pred_0)) * (a_6_y(pred_6) - a_0_y(pred_0))) + ((a_6_z(pred_6) - a_0_z(pred_0)) * (a_6_z(pred_6) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_06, implies(((pwl_06 >= (int)segLower + 1) && (pwl_06 <= (int)segUpper)), (rho_primed_06(pwl_06) == rho_06(c.int_val(pwl_06)) + ((pwl_06 - c.int_val(pwl_06)) * (rho_06(c.int_val(pwl_06) + 1) - rho_06(c.int_val(pwl_06))))))));
			s.add(forall(pwl_60, implies(((pwl_60 >= (int)segLower + 1) && (pwl_60 <= (int)segUpper)), (rho_primed_60(pwl_60) == rho_60(c.int_val(pwl_60)) + ((pwl_60 - c.int_val(pwl_60)) * (rho_60(c.int_val(pwl_60) + 1) - rho_60(c.int_val(pwl_60))))))));
			
			//inverse re-timing
			s.add(forall(t_06, implies(((t_06 >= (int)segLower) && (t_06 <= (int)segUpper)), (rho_60(rho_06(t_06)) == t_06))));

			// ================ AGENT 0 AND AGENT 6 END ================ //
			
			// =============== AGENT 0 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_07 = c.int_const("t_07");
		    s.add(t_07 >= (int)segLower + 1 && t_07 <= (int)segUpper);
		    
		    expr t_before_07 = c.int_const("t_before_07");
		    expr t_after_07 = c.int_const("t_after_07");
		    s.add(t_before_07 >= (int)segLower + 1 && t_before_07 <= (int)segUpper && t_after_07 >= (int)segLower && t_after_07 <= (int)segUpper);
		    
		    func_decl rho_07 = function("rho_07", c.int_sort(), c.int_sort());
		    func_decl rho_primed_07 = function("rho_primed_07", c.real_sort(), c.real_sort());
		    
		    func_decl rho_70 = function("rho_70", c.int_sort(), c.int_sort());
		    func_decl rho_primed_70 = function("rho_primed_70", c.real_sort(), c.real_sort());
		    
		    expr pwl_07 = c.int_const("pwl_07");
		    s.add(pwl_07 >= (int)segLower + 1 && pwl_07 <= (int)segUpper);
		    
		    expr pwl_70 = c.int_const("pwl_70");
		    s.add(pwl_70 >= (int)segLower + 1 && pwl_70 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_07(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_07(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_70(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_70(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_07, t_after_07, implies(((t_before_07 < t_after_07) && (t_before_07 >= (int)segLower + 1) && (t_before_07 <= (int)segUpper) && (t_after_07 >= (int)segLower) && (t_after_07 <= (int)segUpper)), ((rho_07(t_before_07) < rho_07(t_after_07)) && (rho_70(t_before_07) < rho_70(t_after_07))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_7, implies(((rho_07(pred_0) == pred_7) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_0_x(pred_0)) * (a_7_x(pred_7) - a_0_x(pred_0))) + ((a_7_y(pred_7) - a_0_y(pred_0)) * (a_7_y(pred_7) - a_0_y(pred_0))) + ((a_7_z(pred_7) - a_0_z(pred_0)) * (a_7_z(pred_7) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_07, implies(((pwl_07 >= (int)segLower + 1) && (pwl_07 <= (int)segUpper)), (rho_primed_07(pwl_07) == rho_07(c.int_val(pwl_07)) + ((pwl_07 - c.int_val(pwl_07)) * (rho_07(c.int_val(pwl_07) + 1) - rho_07(c.int_val(pwl_07))))))));
			s.add(forall(pwl_70, implies(((pwl_70 >= (int)segLower + 1) && (pwl_70 <= (int)segUpper)), (rho_primed_70(pwl_70) == rho_70(c.int_val(pwl_70)) + ((pwl_70 - c.int_val(pwl_70)) * (rho_70(c.int_val(pwl_70) + 1) - rho_70(c.int_val(pwl_70))))))));
			
			//inverse re-timing
			s.add(forall(t_07, implies(((t_07 >= (int)segLower) && (t_07 <= (int)segUpper)), (rho_70(rho_07(t_07)) == t_07))));

			// ================ AGENT 0 AND AGENT 7 END ================ //
			
			// =============== AGENT 0 AND AGENT 8 START =============== //
			
			//agent pair smt variables
			expr t_08 = c.int_const("t_08");
		    s.add(t_08 >= (int)segLower + 1 && t_08 <= (int)segUpper);
		    
		    expr t_before_08 = c.int_const("t_before_08");
		    expr t_after_08 = c.int_const("t_after_08");
		    s.add(t_before_08 >= (int)segLower + 1 && t_before_08 <= (int)segUpper && t_after_08 >= (int)segLower && t_after_08 <= (int)segUpper);
		    
		    func_decl rho_08 = function("rho_08", c.int_sort(), c.int_sort());
		    func_decl rho_primed_08 = function("rho_primed_08", c.real_sort(), c.real_sort());
		    
		    func_decl rho_80 = function("rho_80", c.int_sort(), c.int_sort());
		    func_decl rho_primed_80 = function("rho_primed_80", c.real_sort(), c.real_sort());
		    
		    expr pwl_08 = c.int_const("pwl_08");
		    s.add(pwl_08 >= (int)segLower + 1 && pwl_08 <= (int)segUpper);
		    
		    expr pwl_80 = c.int_const("pwl_80");
		    s.add(pwl_80 >= (int)segLower + 1 && pwl_80 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_08(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_08(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_80(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_80(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_08, t_after_08, implies(((t_before_08 < t_after_08) && (t_before_08 >= (int)segLower + 1) && (t_before_08 <= (int)segUpper) && (t_after_08 >= (int)segLower) && (t_after_08 <= (int)segUpper)), ((rho_08(t_before_08) < rho_08(t_after_08)) && (rho_80(t_before_08) < rho_80(t_after_08))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_8, implies(((rho_08(pred_0) == pred_8) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_8 >= (int)segLower) && (pred_8 <= (int)segUpper)), (c.real_val(delta) <= (((a_8_x(pred_8) - a_0_x(pred_0)) * (a_8_x(pred_8) - a_0_x(pred_0))) + ((a_8_y(pred_8) - a_0_y(pred_0)) * (a_8_y(pred_8) - a_0_y(pred_0))) + ((a_8_z(pred_8) - a_0_z(pred_0)) * (a_8_z(pred_8) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_08, implies(((pwl_08 >= (int)segLower + 1) && (pwl_08 <= (int)segUpper)), (rho_primed_08(pwl_08) == rho_08(c.int_val(pwl_08)) + ((pwl_08 - c.int_val(pwl_08)) * (rho_08(c.int_val(pwl_08) + 1) - rho_08(c.int_val(pwl_08))))))));
			s.add(forall(pwl_80, implies(((pwl_80 >= (int)segLower + 1) && (pwl_80 <= (int)segUpper)), (rho_primed_80(pwl_80) == rho_80(c.int_val(pwl_80)) + ((pwl_80 - c.int_val(pwl_80)) * (rho_80(c.int_val(pwl_80) + 1) - rho_80(c.int_val(pwl_80))))))));
			
			//inverse re-timing
			s.add(forall(t_08, implies(((t_08 >= (int)segLower) && (t_08 <= (int)segUpper)), (rho_80(rho_08(t_08)) == t_08))));

			// ================ AGENT 0 AND AGENT 8 END ================ //
			
			// =============== AGENT 0 AND AGENT 9 START =============== //
			
			//agent pair smt variables
			expr t_09 = c.int_const("t_09");
		    s.add(t_09 >= (int)segLower + 1 && t_09 <= (int)segUpper);
		    
		    expr t_before_09 = c.int_const("t_before_09");
		    expr t_after_09 = c.int_const("t_after_09");
		    s.add(t_before_09 >= (int)segLower + 1 && t_before_09 <= (int)segUpper && t_after_09 >= (int)segLower && t_after_09 <= (int)segUpper);
		    
		    func_decl rho_09 = function("rho_09", c.int_sort(), c.int_sort());
		    func_decl rho_primed_09 = function("rho_primed_09", c.real_sort(), c.real_sort());
		    
		    func_decl rho_90 = function("rho_90", c.int_sort(), c.int_sort());
		    func_decl rho_primed_90 = function("rho_primed_90", c.real_sort(), c.real_sort());
		    
		    expr pwl_09 = c.int_const("pwl_09");
		    s.add(pwl_09 >= (int)segLower + 1 && pwl_09 <= (int)segUpper);
		    
		    expr pwl_90 = c.int_const("pwl_90");
		    s.add(pwl_90 >= (int)segLower + 1 && pwl_90 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_09(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_09(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_90(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_90(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_09, t_after_09, implies(((t_before_09 < t_after_09) && (t_before_09 >= (int)segLower + 1) && (t_before_09 <= (int)segUpper) && (t_after_09 >= (int)segLower) && (t_after_09 <= (int)segUpper)), ((rho_09(t_before_09) < rho_09(t_after_09)) && (rho_90(t_before_09) < rho_90(t_after_09))))));
			
			//mutual separation constraint
			s.add(forall(pred_0, pred_9, implies(((rho_09(pred_0) == pred_9) && (pred_0 >= (int)segLower + 1) && (pred_0 <= (int)segUpper) && (pred_9 >= (int)segLower) && (pred_9 <= (int)segUpper)), (c.real_val(delta) <= (((a_9_x(pred_9) - a_0_x(pred_0)) * (a_9_x(pred_9) - a_0_x(pred_0))) + ((a_9_y(pred_9) - a_0_y(pred_0)) * (a_9_y(pred_9) - a_0_y(pred_0))) + ((a_9_z(pred_9) - a_0_z(pred_0)) * (a_9_z(pred_9) - a_0_z(pred_0))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_09, implies(((pwl_09 >= (int)segLower + 1) && (pwl_09 <= (int)segUpper)), (rho_primed_09(pwl_09) == rho_09(c.int_val(pwl_09)) + ((pwl_09 - c.int_val(pwl_09)) * (rho_09(c.int_val(pwl_09) + 1) - rho_09(c.int_val(pwl_09))))))));
			s.add(forall(pwl_90, implies(((pwl_90 >= (int)segLower + 1) && (pwl_90 <= (int)segUpper)), (rho_primed_90(pwl_90) == rho_90(c.int_val(pwl_90)) + ((pwl_90 - c.int_val(pwl_90)) * (rho_90(c.int_val(pwl_90) + 1) - rho_90(c.int_val(pwl_90))))))));
			
			//inverse re-timing
			s.add(forall(t_09, implies(((t_09 >= (int)segLower) && (t_09 <= (int)segUpper)), (rho_90(rho_09(t_09)) == t_09))));

			// ================ AGENT 0 AND AGENT 9 END ================ //
			
			// =============== AGENT 1 AND AGENT 2 START =============== //
			
			//agent pair smt variables
			expr t_12 = c.int_const("t_12");
		    s.add(t_12 >= (int)segLower + 1 && t_12 <= (int)segUpper);
		    
		    expr t_before_12 = c.int_const("t_before_12");
		    expr t_after_12 = c.int_const("t_after_12");
		    s.add(t_before_12 >= (int)segLower + 1 && t_before_12 <= (int)segUpper && t_after_12 >= (int)segLower && t_after_12 <= (int)segUpper);
		    
		    func_decl rho_12 = function("rho_12", c.int_sort(), c.int_sort());
		    func_decl rho_primed_12 = function("rho_primed_12", c.real_sort(), c.real_sort());
		    
		    func_decl rho_21 = function("rho_21", c.int_sort(), c.int_sort());
		    func_decl rho_primed_21 = function("rho_primed_21", c.real_sort(), c.real_sort());
		    
		    expr pwl_12 = c.int_const("pwl_12");
		    s.add(pwl_12 >= (int)segLower + 1 && pwl_12 <= (int)segUpper);
		    
		    expr pwl_21 = c.int_const("pwl_21");
		    s.add(pwl_21 >= (int)segLower + 1 && pwl_21 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_12(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_12(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_21(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_21(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_12, t_after_12, implies(((t_before_12 < t_after_12) && (t_before_12 >= (int)segLower + 1) && (t_before_12 <= (int)segUpper) && (t_after_12 >= (int)segLower) && (t_after_12 <= (int)segUpper)), ((rho_12(t_before_12) < rho_12(t_after_12)) && (rho_21(t_before_12) < rho_21(t_after_12))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_2, implies(((rho_12(pred_1) == pred_2) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_2 >= (int)segLower) && (pred_2 <= (int)segUpper)), (c.real_val(delta) <= (((a_2_x(pred_2) - a_1_x(pred_1)) * (a_2_x(pred_2) - a_1_x(pred_1))) + ((a_2_y(pred_2) - a_1_y(pred_1)) * (a_2_y(pred_2) - a_1_y(pred_1))) + ((a_2_z(pred_2) - a_1_z(pred_1)) * (a_2_z(pred_2) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_12, implies(((pwl_12 >= (int)segLower + 1) && (pwl_12 <= (int)segUpper)), (rho_primed_12(pwl_12) == rho_12(c.int_val(pwl_12)) + ((pwl_12 - c.int_val(pwl_12)) * (rho_12(c.int_val(pwl_12) + 1) - rho_12(c.int_val(pwl_12))))))));
			s.add(forall(pwl_21, implies(((pwl_21 >= (int)segLower + 1) && (pwl_21 <= (int)segUpper)), (rho_primed_21(pwl_21) == rho_21(c.int_val(pwl_21)) + ((pwl_21 - c.int_val(pwl_21)) * (rho_21(c.int_val(pwl_21) + 1) - rho_21(c.int_val(pwl_21))))))));
			
			//inverse re-timing
			s.add(forall(t_12, implies(((t_12 >= (int)segLower) && (t_12 <= (int)segUpper)), (rho_21(rho_12(t_12)) == t_12))));

			// ================ AGENT 1 AND AGENT 2 END ================ //
			
			// =============== AGENT 1 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_13 = c.int_const("t_13");
		    s.add(t_13 >= (int)segLower + 1 && t_13 <= (int)segUpper);
		    
		    expr t_before_13 = c.int_const("t_before_13");
		    expr t_after_13 = c.int_const("t_after_13");
		    s.add(t_before_13 >= (int)segLower + 1 && t_before_13 <= (int)segUpper && t_after_13 >= (int)segLower && t_after_13 <= (int)segUpper);
		    
		    func_decl rho_13 = function("rho_13", c.int_sort(), c.int_sort());
		    func_decl rho_primed_13 = function("rho_primed_13", c.real_sort(), c.real_sort());
		    
		    func_decl rho_31 = function("rho_31", c.int_sort(), c.int_sort());
		    func_decl rho_primed_31 = function("rho_primed_31", c.real_sort(), c.real_sort());
		    
		    expr pwl_13 = c.int_const("pwl_13");
		    s.add(pwl_13 >= (int)segLower + 1 && pwl_13 <= (int)segUpper);
		    
		    expr pwl_31 = c.int_const("pwl_31");
		    s.add(pwl_31 >= (int)segLower + 1 && pwl_31 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_13(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_13(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_31(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_31(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_13, t_after_13, implies(((t_before_13 < t_after_13) && (t_before_13 >= (int)segLower + 1) && (t_before_13 <= (int)segUpper) && (t_after_13 >= (int)segLower) && (t_after_13 <= (int)segUpper)), ((rho_13(t_before_13) < rho_13(t_after_13)) && (rho_31(t_before_13) < rho_31(t_after_13))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_3, implies(((rho_13(pred_1) == pred_3) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_1_x(pred_1)) * (a_3_x(pred_3) - a_1_x(pred_1))) + ((a_3_y(pred_3) - a_1_y(pred_1)) * (a_3_y(pred_3) - a_1_y(pred_1))) + ((a_3_z(pred_3) - a_1_z(pred_1)) * (a_3_z(pred_3) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_13, implies(((pwl_13 >= (int)segLower + 1) && (pwl_13 <= (int)segUpper)), (rho_primed_13(pwl_13) == rho_13(c.int_val(pwl_13)) + ((pwl_13 - c.int_val(pwl_13)) * (rho_13(c.int_val(pwl_13) + 1) - rho_13(c.int_val(pwl_13))))))));
			s.add(forall(pwl_31, implies(((pwl_31 >= (int)segLower + 1) && (pwl_31 <= (int)segUpper)), (rho_primed_31(pwl_31) == rho_31(c.int_val(pwl_31)) + ((pwl_31 - c.int_val(pwl_31)) * (rho_31(c.int_val(pwl_31) + 1) - rho_31(c.int_val(pwl_31))))))));
			
			//inverse re-timing
			s.add(forall(t_13, implies(((t_13 >= (int)segLower) && (t_13 <= (int)segUpper)), (rho_31(rho_13(t_13)) == t_13))));

			// ================ AGENT 1 AND AGENT 3 END ================ //
			
			// =============== AGENT 1 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_14 = c.int_const("t_14");
		    s.add(t_14 >= (int)segLower + 1 && t_14 <= (int)segUpper);
		    
		    expr t_before_14 = c.int_const("t_before_14");
		    expr t_after_14 = c.int_const("t_after_14");
		    s.add(t_before_14 >= (int)segLower + 1 && t_before_14 <= (int)segUpper && t_after_14 >= (int)segLower && t_after_14 <= (int)segUpper);
		    
		    func_decl rho_14 = function("rho_14", c.int_sort(), c.int_sort());
		    func_decl rho_primed_14 = function("rho_primed_14", c.real_sort(), c.real_sort());
		    
		    func_decl rho_41 = function("rho_41", c.int_sort(), c.int_sort());
		    func_decl rho_primed_41 = function("rho_primed_41", c.real_sort(), c.real_sort());
		    
		    expr pwl_14 = c.int_const("pwl_14");
		    s.add(pwl_14 >= (int)segLower + 1 && pwl_14 <= (int)segUpper);
		    
		    expr pwl_41 = c.int_const("pwl_41");
		    s.add(pwl_41 >= (int)segLower + 1 && pwl_41 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_14(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_14(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_41(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_41(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_14, t_after_14, implies(((t_before_14 < t_after_14) && (t_before_14 >= (int)segLower + 1) && (t_before_14 <= (int)segUpper) && (t_after_14 >= (int)segLower) && (t_after_14 <= (int)segUpper)), ((rho_14(t_before_14) < rho_14(t_after_14)) && (rho_41(t_before_14) < rho_41(t_after_14))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_4, implies(((rho_14(pred_1) == pred_4) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_1_x(pred_1)) * (a_4_x(pred_4) - a_1_x(pred_1))) + ((a_4_y(pred_4) - a_1_y(pred_1)) * (a_4_y(pred_4) - a_1_y(pred_1))) + ((a_4_z(pred_4) - a_1_z(pred_1)) * (a_4_z(pred_4) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_14, implies(((pwl_14 >= (int)segLower + 1) && (pwl_14 <= (int)segUpper)), (rho_primed_14(pwl_14) == rho_14(c.int_val(pwl_14)) + ((pwl_14 - c.int_val(pwl_14)) * (rho_14(c.int_val(pwl_14) + 1) - rho_14(c.int_val(pwl_14))))))));
			s.add(forall(pwl_41, implies(((pwl_41 >= (int)segLower + 1) && (pwl_41 <= (int)segUpper)), (rho_primed_41(pwl_41) == rho_41(c.int_val(pwl_41)) + ((pwl_41 - c.int_val(pwl_41)) * (rho_41(c.int_val(pwl_41) + 1) - rho_41(c.int_val(pwl_41))))))));
			
			//inverse re-timing
			s.add(forall(t_14, implies(((t_14 >= (int)segLower) && (t_14 <= (int)segUpper)), (rho_41(rho_14(t_14)) == t_14))));

			// ================ AGENT 1 AND AGENT 4 END ================ //
			
			// =============== AGENT 1 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_15 = c.int_const("t_15");
		    s.add(t_15 >= (int)segLower + 1 && t_15 <= (int)segUpper);
		    
		    expr t_before_15 = c.int_const("t_before_15");
		    expr t_after_15 = c.int_const("t_after_15");
		    s.add(t_before_15 >= (int)segLower + 1 && t_before_15 <= (int)segUpper && t_after_15 >= (int)segLower && t_after_15 <= (int)segUpper);
		    
		    func_decl rho_15 = function("rho_15", c.int_sort(), c.int_sort());
		    func_decl rho_primed_15 = function("rho_primed_15", c.real_sort(), c.real_sort());
		    
		    func_decl rho_51 = function("rho_51", c.int_sort(), c.int_sort());
		    func_decl rho_primed_51 = function("rho_primed_51", c.real_sort(), c.real_sort());
		    
		    expr pwl_15 = c.int_const("pwl_15");
		    s.add(pwl_15 >= (int)segLower + 1 && pwl_15 <= (int)segUpper);
		    
		    expr pwl_51 = c.int_const("pwl_51");
		    s.add(pwl_51 >= (int)segLower + 1 && pwl_51 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_15(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_15(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_51(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_51(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_15, t_after_15, implies(((t_before_15 < t_after_15) && (t_before_15 >= (int)segLower + 1) && (t_before_15 <= (int)segUpper) && (t_after_15 >= (int)segLower) && (t_after_15 <= (int)segUpper)), ((rho_15(t_before_15) < rho_15(t_after_15)) && (rho_51(t_before_15) < rho_51(t_after_15))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_5, implies(((rho_15(pred_1) == pred_5) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_1_x(pred_1)) * (a_5_x(pred_5) - a_1_x(pred_1))) + ((a_5_y(pred_5) - a_1_y(pred_1)) * (a_5_y(pred_5) - a_1_y(pred_1))) + ((a_5_z(pred_5) - a_1_z(pred_1)) * (a_5_z(pred_5) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_15, implies(((pwl_15 >= (int)segLower + 1) && (pwl_15 <= (int)segUpper)), (rho_primed_15(pwl_15) == rho_15(c.int_val(pwl_15)) + ((pwl_15 - c.int_val(pwl_15)) * (rho_15(c.int_val(pwl_15) + 1) - rho_15(c.int_val(pwl_15))))))));
			s.add(forall(pwl_51, implies(((pwl_51 >= (int)segLower + 1) && (pwl_51 <= (int)segUpper)), (rho_primed_51(pwl_51) == rho_51(c.int_val(pwl_51)) + ((pwl_51 - c.int_val(pwl_51)) * (rho_51(c.int_val(pwl_51) + 1) - rho_51(c.int_val(pwl_51))))))));
			
			//inverse re-timing
			s.add(forall(t_15, implies(((t_15 >= (int)segLower) && (t_15 <= (int)segUpper)), (rho_51(rho_15(t_15)) == t_15))));

			// ================ AGENT 1 AND AGENT 5 END ================ //
			
			// =============== AGENT 1 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_16 = c.int_const("t_16");
		    s.add(t_16 >= (int)segLower + 1 && t_16 <= (int)segUpper);
		    
		    expr t_before_16 = c.int_const("t_before_16");
		    expr t_after_16 = c.int_const("t_after_16");
		    s.add(t_before_16 >= (int)segLower + 1 && t_before_16 <= (int)segUpper && t_after_16 >= (int)segLower && t_after_16 <= (int)segUpper);
		    
		    func_decl rho_16 = function("rho_16", c.int_sort(), c.int_sort());
		    func_decl rho_primed_16 = function("rho_primed_16", c.real_sort(), c.real_sort());
		    
		    func_decl rho_61 = function("rho_61", c.int_sort(), c.int_sort());
		    func_decl rho_primed_61 = function("rho_primed_61", c.real_sort(), c.real_sort());
		    
		    expr pwl_16 = c.int_const("pwl_16");
		    s.add(pwl_16 >= (int)segLower + 1 && pwl_16 <= (int)segUpper);
		    
		    expr pwl_61 = c.int_const("pwl_61");
		    s.add(pwl_61 >= (int)segLower + 1 && pwl_61 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_16(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_16(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_61(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_61(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_16, t_after_16, implies(((t_before_16 < t_after_16) && (t_before_16 >= (int)segLower + 1) && (t_before_16 <= (int)segUpper) && (t_after_16 >= (int)segLower) && (t_after_16 <= (int)segUpper)), ((rho_16(t_before_16) < rho_16(t_after_16)) && (rho_61(t_before_16) < rho_61(t_after_16))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_6, implies(((rho_16(pred_1) == pred_6) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_1_x(pred_1)) * (a_6_x(pred_6) - a_1_x(pred_1))) + ((a_6_y(pred_6) - a_1_y(pred_1)) * (a_6_y(pred_6) - a_1_y(pred_1))) + ((a_6_z(pred_6) - a_1_z(pred_1)) * (a_6_z(pred_6) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_16, implies(((pwl_16 >= (int)segLower + 1) && (pwl_16 <= (int)segUpper)), (rho_primed_16(pwl_16) == rho_16(c.int_val(pwl_16)) + ((pwl_16 - c.int_val(pwl_16)) * (rho_16(c.int_val(pwl_16) + 1) - rho_16(c.int_val(pwl_16))))))));
			s.add(forall(pwl_61, implies(((pwl_61 >= (int)segLower + 1) && (pwl_61 <= (int)segUpper)), (rho_primed_61(pwl_61) == rho_61(c.int_val(pwl_61)) + ((pwl_61 - c.int_val(pwl_61)) * (rho_61(c.int_val(pwl_61) + 1) - rho_61(c.int_val(pwl_61))))))));
			
			//inverse re-timing
			s.add(forall(t_16, implies(((t_16 >= (int)segLower) && (t_16 <= (int)segUpper)), (rho_61(rho_16(t_16)) == t_16))));

			// ================ AGENT 1 AND AGENT 6 END ================ //
			
			// =============== AGENT 1 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_17 = c.int_const("t_17");
		    s.add(t_17 >= (int)segLower + 1 && t_17 <= (int)segUpper);
		    
		    expr t_before_17 = c.int_const("t_before_17");
		    expr t_after_17 = c.int_const("t_after_17");
		    s.add(t_before_17 >= (int)segLower + 1 && t_before_17 <= (int)segUpper && t_after_17 >= (int)segLower && t_after_17 <= (int)segUpper);
		    
		    func_decl rho_17 = function("rho_17", c.int_sort(), c.int_sort());
		    func_decl rho_primed_17 = function("rho_primed_17", c.real_sort(), c.real_sort());
		    
		    func_decl rho_71 = function("rho_71", c.int_sort(), c.int_sort());
		    func_decl rho_primed_71 = function("rho_primed_71", c.real_sort(), c.real_sort());
		    
		    expr pwl_17 = c.int_const("pwl_17");
		    s.add(pwl_17 >= (int)segLower + 1 && pwl_17 <= (int)segUpper);
		    
		    expr pwl_71 = c.int_const("pwl_71");
		    s.add(pwl_71 >= (int)segLower + 1 && pwl_71 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_17(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_17(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_71(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_71(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_17, t_after_17, implies(((t_before_17 < t_after_17) && (t_before_17 >= (int)segLower + 1) && (t_before_17 <= (int)segUpper) && (t_after_17 >= (int)segLower) && (t_after_17 <= (int)segUpper)), ((rho_17(t_before_17) < rho_17(t_after_17)) && (rho_71(t_before_17) < rho_71(t_after_17))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_7, implies(((rho_17(pred_1) == pred_7) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_1_x(pred_1)) * (a_7_x(pred_7) - a_1_x(pred_1))) + ((a_7_y(pred_7) - a_1_y(pred_1)) * (a_7_y(pred_7) - a_1_y(pred_1))) + ((a_7_z(pred_7) - a_1_z(pred_1)) * (a_7_z(pred_7) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_17, implies(((pwl_17 >= (int)segLower + 1) && (pwl_17 <= (int)segUpper)), (rho_primed_17(pwl_17) == rho_17(c.int_val(pwl_17)) + ((pwl_17 - c.int_val(pwl_17)) * (rho_17(c.int_val(pwl_17) + 1) - rho_17(c.int_val(pwl_17))))))));
			s.add(forall(pwl_71, implies(((pwl_71 >= (int)segLower + 1) && (pwl_71 <= (int)segUpper)), (rho_primed_71(pwl_71) == rho_71(c.int_val(pwl_71)) + ((pwl_71 - c.int_val(pwl_71)) * (rho_71(c.int_val(pwl_71) + 1) - rho_71(c.int_val(pwl_71))))))));
			
			//inverse re-timing
			s.add(forall(t_17, implies(((t_17 >= (int)segLower) && (t_17 <= (int)segUpper)), (rho_71(rho_17(t_17)) == t_17))));

			// ================ AGENT 1 AND AGENT 7 END ================ //
			
			// =============== AGENT 1 AND AGENT 8 START =============== //
			
			//agent pair smt variables
			expr t_18 = c.int_const("t_18");
		    s.add(t_18 >= (int)segLower + 1 && t_18 <= (int)segUpper);
		    
		    expr t_before_18 = c.int_const("t_before_18");
		    expr t_after_18 = c.int_const("t_after_18");
		    s.add(t_before_18 >= (int)segLower + 1 && t_before_18 <= (int)segUpper && t_after_18 >= (int)segLower && t_after_18 <= (int)segUpper);
		    
		    func_decl rho_18 = function("rho_18", c.int_sort(), c.int_sort());
		    func_decl rho_primed_18 = function("rho_primed_18", c.real_sort(), c.real_sort());
		    
		    func_decl rho_81 = function("rho_81", c.int_sort(), c.int_sort());
		    func_decl rho_primed_81 = function("rho_primed_81", c.real_sort(), c.real_sort());
		    
		    expr pwl_18 = c.int_const("pwl_18");
		    s.add(pwl_18 >= (int)segLower + 1 && pwl_18 <= (int)segUpper);
		    
		    expr pwl_81 = c.int_const("pwl_81");
		    s.add(pwl_81 >= (int)segLower + 1 && pwl_81 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_18(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_18(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_81(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_81(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_18, t_after_18, implies(((t_before_18 < t_after_18) && (t_before_18 >= (int)segLower + 1) && (t_before_18 <= (int)segUpper) && (t_after_18 >= (int)segLower) && (t_after_18 <= (int)segUpper)), ((rho_18(t_before_18) < rho_18(t_after_18)) && (rho_81(t_before_18) < rho_81(t_after_18))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_8, implies(((rho_18(pred_1) == pred_8) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_8 >= (int)segLower) && (pred_8 <= (int)segUpper)), (c.real_val(delta) <= (((a_8_x(pred_8) - a_1_x(pred_1)) * (a_8_x(pred_8) - a_1_x(pred_1))) + ((a_8_y(pred_8) - a_1_y(pred_1)) * (a_8_y(pred_8) - a_1_y(pred_1))) + ((a_8_z(pred_8) - a_1_z(pred_1)) * (a_8_z(pred_8) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_18, implies(((pwl_18 >= (int)segLower + 1) && (pwl_18 <= (int)segUpper)), (rho_primed_18(pwl_18) == rho_18(c.int_val(pwl_18)) + ((pwl_18 - c.int_val(pwl_18)) * (rho_18(c.int_val(pwl_18) + 1) - rho_18(c.int_val(pwl_18))))))));
			s.add(forall(pwl_81, implies(((pwl_81 >= (int)segLower + 1) && (pwl_81 <= (int)segUpper)), (rho_primed_81(pwl_81) == rho_81(c.int_val(pwl_81)) + ((pwl_81 - c.int_val(pwl_81)) * (rho_81(c.int_val(pwl_81) + 1) - rho_81(c.int_val(pwl_81))))))));
			
			//inverse re-timing
			s.add(forall(t_18, implies(((t_18 >= (int)segLower) && (t_18 <= (int)segUpper)), (rho_81(rho_18(t_18)) == t_18))));

			// ================ AGENT 1 AND AGENT 8 END ================ //
			
			// =============== AGENT 1 AND AGENT 9 START =============== //
			
			//agent pair smt variables
			expr t_19 = c.int_const("t_19");
		    s.add(t_19 >= (int)segLower + 1 && t_19 <= (int)segUpper);
		    
		    expr t_before_19 = c.int_const("t_before_19");
		    expr t_after_19 = c.int_const("t_after_19");
		    s.add(t_before_19 >= (int)segLower + 1 && t_before_19 <= (int)segUpper && t_after_19 >= (int)segLower && t_after_19 <= (int)segUpper);
		    
		    func_decl rho_19 = function("rho_19", c.int_sort(), c.int_sort());
		    func_decl rho_primed_19 = function("rho_primed_19", c.real_sort(), c.real_sort());
		    
		    func_decl rho_91 = function("rho_91", c.int_sort(), c.int_sort());
		    func_decl rho_primed_91 = function("rho_primed_91", c.real_sort(), c.real_sort());
		    
		    expr pwl_19 = c.int_const("pwl_19");
		    s.add(pwl_19 >= (int)segLower + 1 && pwl_19 <= (int)segUpper);
		    
		    expr pwl_91 = c.int_const("pwl_91");
		    s.add(pwl_91 >= (int)segLower + 1 && pwl_91 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_19(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_19(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_91(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_91(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_19, t_after_19, implies(((t_before_19 < t_after_19) && (t_before_19 >= (int)segLower + 1) && (t_before_19 <= (int)segUpper) && (t_after_19 >= (int)segLower) && (t_after_19 <= (int)segUpper)), ((rho_19(t_before_19) < rho_19(t_after_19)) && (rho_91(t_before_19) < rho_91(t_after_19))))));
			
			//mutual separation constraint
			s.add(forall(pred_1, pred_9, implies(((rho_19(pred_1) == pred_9) && (pred_1 >= (int)segLower + 1) && (pred_1 <= (int)segUpper) && (pred_9 >= (int)segLower) && (pred_9 <= (int)segUpper)), (c.real_val(delta) <= (((a_9_x(pred_9) - a_1_x(pred_1)) * (a_9_x(pred_9) - a_1_x(pred_1))) + ((a_9_y(pred_9) - a_1_y(pred_1)) * (a_9_y(pred_9) - a_1_y(pred_1))) + ((a_9_z(pred_9) - a_1_z(pred_1)) * (a_9_z(pred_9) - a_1_z(pred_1))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_19, implies(((pwl_19 >= (int)segLower + 1) && (pwl_19 <= (int)segUpper)), (rho_primed_19(pwl_19) == rho_19(c.int_val(pwl_19)) + ((pwl_19 - c.int_val(pwl_19)) * (rho_19(c.int_val(pwl_19) + 1) - rho_19(c.int_val(pwl_19))))))));
			s.add(forall(pwl_91, implies(((pwl_91 >= (int)segLower + 1) && (pwl_91 <= (int)segUpper)), (rho_primed_91(pwl_91) == rho_91(c.int_val(pwl_91)) + ((pwl_91 - c.int_val(pwl_91)) * (rho_91(c.int_val(pwl_91) + 1) - rho_91(c.int_val(pwl_91))))))));
			
			//inverse re-timing
			s.add(forall(t_19, implies(((t_19 >= (int)segLower) && (t_19 <= (int)segUpper)), (rho_91(rho_19(t_19)) == t_19))));

			// ================ AGENT 1 AND AGENT 9 END ================ //
			
			// =============== AGENT 2 AND AGENT 3 START =============== //
			
			//agent pair smt variables
			expr t_23 = c.int_const("t_23");
		    s.add(t_23 >= (int)segLower + 1 && t_23 <= (int)segUpper);
		    
		    expr t_before_23 = c.int_const("t_before_23");
		    expr t_after_23 = c.int_const("t_after_23");
		    s.add(t_before_23 >= (int)segLower + 1 && t_before_23 <= (int)segUpper && t_after_23 >= (int)segLower && t_after_23 <= (int)segUpper);
		    
		    func_decl rho_23 = function("rho_23", c.int_sort(), c.int_sort());
		    func_decl rho_primed_23 = function("rho_primed_23", c.real_sort(), c.real_sort());
		    
		    func_decl rho_32 = function("rho_32", c.int_sort(), c.int_sort());
		    func_decl rho_primed_32 = function("rho_primed_32", c.real_sort(), c.real_sort());
		    
		    expr pwl_23 = c.int_const("pwl_23");
		    s.add(pwl_23 >= (int)segLower + 1 && pwl_23 <= (int)segUpper);
		    
		    expr pwl_32 = c.int_const("pwl_32");
		    s.add(pwl_32 >= (int)segLower + 1 && pwl_32 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_23(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_23(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_32(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_32(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_23, t_after_23, implies(((t_before_23 < t_after_23) && (t_before_23 >= (int)segLower + 1) && (t_before_23 <= (int)segUpper) && (t_after_23 >= (int)segLower) && (t_after_23 <= (int)segUpper)), ((rho_23(t_before_23) < rho_23(t_after_23)) && (rho_32(t_before_23) < rho_32(t_after_23))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_3, implies(((rho_23(pred_2) == pred_3) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_3 >= (int)segLower) && (pred_3 <= (int)segUpper)), (c.real_val(delta) <= (((a_3_x(pred_3) - a_2_x(pred_2)) * (a_3_x(pred_3) - a_2_x(pred_2))) + ((a_3_y(pred_3) - a_2_y(pred_2)) * (a_3_y(pred_3) - a_2_y(pred_2))) + ((a_3_z(pred_3) - a_2_z(pred_2)) * (a_3_z(pred_3) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_23, implies(((pwl_23 >= (int)segLower + 1) && (pwl_23 <= (int)segUpper)), (rho_primed_23(pwl_23) == rho_23(c.int_val(pwl_23)) + ((pwl_23 - c.int_val(pwl_23)) * (rho_23(c.int_val(pwl_23) + 1) - rho_23(c.int_val(pwl_23))))))));
			s.add(forall(pwl_32, implies(((pwl_32 >= (int)segLower + 1) && (pwl_32 <= (int)segUpper)), (rho_primed_32(pwl_32) == rho_32(c.int_val(pwl_32)) + ((pwl_32 - c.int_val(pwl_32)) * (rho_32(c.int_val(pwl_32) + 1) - rho_32(c.int_val(pwl_32))))))));
			
			//inverse re-timing
			s.add(forall(t_23, implies(((t_23 >= (int)segLower) && (t_23 <= (int)segUpper)), (rho_32(rho_23(t_23)) == t_23))));

			// ================ AGENT 2 AND AGENT 3 END ================ //
			
			// =============== AGENT 2 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_24 = c.int_const("t_24");
		    s.add(t_24 >= (int)segLower + 1 && t_24 <= (int)segUpper);
		    
		    expr t_before_24 = c.int_const("t_before_24");
		    expr t_after_24 = c.int_const("t_after_24");
		    s.add(t_before_24 >= (int)segLower + 1 && t_before_24 <= (int)segUpper && t_after_24 >= (int)segLower && t_after_24 <= (int)segUpper);
		    
		    func_decl rho_24 = function("rho_24", c.int_sort(), c.int_sort());
		    func_decl rho_primed_24 = function("rho_primed_24", c.real_sort(), c.real_sort());
		    
		    func_decl rho_42 = function("rho_42", c.int_sort(), c.int_sort());
		    func_decl rho_primed_42 = function("rho_primed_42", c.real_sort(), c.real_sort());
		    
		    expr pwl_24 = c.int_const("pwl_24");
		    s.add(pwl_24 >= (int)segLower + 1 && pwl_24 <= (int)segUpper);
		    
		    expr pwl_42 = c.int_const("pwl_42");
		    s.add(pwl_42 >= (int)segLower + 1 && pwl_42 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_24(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_24(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_42(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_42(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_24, t_after_24, implies(((t_before_24 < t_after_24) && (t_before_24 >= (int)segLower + 1) && (t_before_24 <= (int)segUpper) && (t_after_24 >= (int)segLower) && (t_after_24 <= (int)segUpper)), ((rho_24(t_before_24) < rho_24(t_after_24)) && (rho_42(t_before_24) < rho_42(t_after_24))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_4, implies(((rho_24(pred_2) == pred_4) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_2_x(pred_2)) * (a_4_x(pred_4) - a_2_x(pred_2))) + ((a_4_y(pred_4) - a_2_y(pred_2)) * (a_4_y(pred_4) - a_2_y(pred_2))) + ((a_4_z(pred_4) - a_2_z(pred_2)) * (a_4_z(pred_4) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_24, implies(((pwl_24 >= (int)segLower + 1) && (pwl_24 <= (int)segUpper)), (rho_primed_24(pwl_24) == rho_24(c.int_val(pwl_24)) + ((pwl_24 - c.int_val(pwl_24)) * (rho_24(c.int_val(pwl_24) + 1) - rho_24(c.int_val(pwl_24))))))));
			s.add(forall(pwl_42, implies(((pwl_42 >= (int)segLower + 1) && (pwl_42 <= (int)segUpper)), (rho_primed_42(pwl_42) == rho_42(c.int_val(pwl_42)) + ((pwl_42 - c.int_val(pwl_42)) * (rho_42(c.int_val(pwl_42) + 1) - rho_42(c.int_val(pwl_42))))))));
			
			//inverse re-timing
			s.add(forall(t_24, implies(((t_24 >= (int)segLower) && (t_24 <= (int)segUpper)), (rho_42(rho_24(t_24)) == t_24))));

			// ================ AGENT 2 AND AGENT 4 END ================ //
			
			// =============== AGENT 2 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_25 = c.int_const("t_25");
		    s.add(t_25 >= (int)segLower + 1 && t_25 <= (int)segUpper);
		    
		    expr t_before_25 = c.int_const("t_before_25");
		    expr t_after_25 = c.int_const("t_after_25");
		    s.add(t_before_25 >= (int)segLower + 1 && t_before_25 <= (int)segUpper && t_after_25 >= (int)segLower && t_after_25 <= (int)segUpper);
		    
		    func_decl rho_25 = function("rho_25", c.int_sort(), c.int_sort());
		    func_decl rho_primed_25 = function("rho_primed_25", c.real_sort(), c.real_sort());
		    
		    func_decl rho_52 = function("rho_52", c.int_sort(), c.int_sort());
		    func_decl rho_primed_52 = function("rho_primed_52", c.real_sort(), c.real_sort());
		    
		    expr pwl_25 = c.int_const("pwl_25");
		    s.add(pwl_25 >= (int)segLower + 1 && pwl_25 <= (int)segUpper);
		    
		    expr pwl_52 = c.int_const("pwl_52");
		    s.add(pwl_52 >= (int)segLower + 1 && pwl_52 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_25(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_25(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_52(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_52(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_25, t_after_25, implies(((t_before_25 < t_after_25) && (t_before_25 >= (int)segLower + 1) && (t_before_25 <= (int)segUpper) && (t_after_25 >= (int)segLower) && (t_after_25 <= (int)segUpper)), ((rho_25(t_before_25) < rho_25(t_after_25)) && (rho_52(t_before_25) < rho_52(t_after_25))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_5, implies(((rho_25(pred_2) == pred_5) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_2_x(pred_2)) * (a_5_x(pred_5) - a_2_x(pred_2))) + ((a_5_y(pred_5) - a_2_y(pred_2)) * (a_5_y(pred_5) - a_2_y(pred_2))) + ((a_5_z(pred_5) - a_2_z(pred_2)) * (a_5_z(pred_5) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_25, implies(((pwl_25 >= (int)segLower + 1) && (pwl_25 <= (int)segUpper)), (rho_primed_25(pwl_25) == rho_25(c.int_val(pwl_25)) + ((pwl_25 - c.int_val(pwl_25)) * (rho_25(c.int_val(pwl_25) + 1) - rho_25(c.int_val(pwl_25))))))));
			s.add(forall(pwl_52, implies(((pwl_52 >= (int)segLower + 1) && (pwl_52 <= (int)segUpper)), (rho_primed_52(pwl_52) == rho_52(c.int_val(pwl_52)) + ((pwl_52 - c.int_val(pwl_52)) * (rho_52(c.int_val(pwl_52) + 1) - rho_52(c.int_val(pwl_52))))))));
			
			//inverse re-timing
			s.add(forall(t_25, implies(((t_25 >= (int)segLower) && (t_25 <= (int)segUpper)), (rho_52(rho_25(t_25)) == t_25))));

			// ================ AGENT 2 AND AGENT 5 END ================ //
			
			// =============== AGENT 2 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_26 = c.int_const("t_26");
		    s.add(t_26 >= (int)segLower + 1 && t_26 <= (int)segUpper);
		    
		    expr t_before_26 = c.int_const("t_before_26");
		    expr t_after_26 = c.int_const("t_after_26");
		    s.add(t_before_26 >= (int)segLower + 1 && t_before_26 <= (int)segUpper && t_after_26 >= (int)segLower && t_after_26 <= (int)segUpper);
		    
		    func_decl rho_26 = function("rho_26", c.int_sort(), c.int_sort());
		    func_decl rho_primed_26 = function("rho_primed_26", c.real_sort(), c.real_sort());
		    
		    func_decl rho_62 = function("rho_62", c.int_sort(), c.int_sort());
		    func_decl rho_primed_62 = function("rho_primed_62", c.real_sort(), c.real_sort());
		    
		    expr pwl_26 = c.int_const("pwl_26");
		    s.add(pwl_26 >= (int)segLower + 1 && pwl_26 <= (int)segUpper);
		    
		    expr pwl_62 = c.int_const("pwl_62");
		    s.add(pwl_62 >= (int)segLower + 1 && pwl_62 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_26(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_26(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_62(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_62(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_26, t_after_26, implies(((t_before_26 < t_after_26) && (t_before_26 >= (int)segLower + 1) && (t_before_26 <= (int)segUpper) && (t_after_26 >= (int)segLower) && (t_after_26 <= (int)segUpper)), ((rho_26(t_before_26) < rho_26(t_after_26)) && (rho_62(t_before_26) < rho_62(t_after_26))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_6, implies(((rho_26(pred_2) == pred_6) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_2_x(pred_2)) * (a_6_x(pred_6) - a_2_x(pred_2))) + ((a_6_y(pred_6) - a_2_y(pred_2)) * (a_6_y(pred_6) - a_2_y(pred_2))) + ((a_6_z(pred_6) - a_2_z(pred_2)) * (a_6_z(pred_6) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_26, implies(((pwl_26 >= (int)segLower + 1) && (pwl_26 <= (int)segUpper)), (rho_primed_26(pwl_26) == rho_26(c.int_val(pwl_26)) + ((pwl_26 - c.int_val(pwl_26)) * (rho_26(c.int_val(pwl_26) + 1) - rho_26(c.int_val(pwl_26))))))));
			s.add(forall(pwl_62, implies(((pwl_62 >= (int)segLower + 1) && (pwl_62 <= (int)segUpper)), (rho_primed_62(pwl_62) == rho_62(c.int_val(pwl_62)) + ((pwl_62 - c.int_val(pwl_62)) * (rho_62(c.int_val(pwl_62) + 1) - rho_62(c.int_val(pwl_62))))))));
			
			//inverse re-timing
			s.add(forall(t_26, implies(((t_26 >= (int)segLower) && (t_26 <= (int)segUpper)), (rho_62(rho_26(t_26)) == t_26))));

			// ================ AGENT 2 AND AGENT 6 END ================ //
			
			// =============== AGENT 2 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_27 = c.int_const("t_27");
		    s.add(t_27 >= (int)segLower + 1 && t_27 <= (int)segUpper);
		    
		    expr t_before_27 = c.int_const("t_before_27");
		    expr t_after_27 = c.int_const("t_after_27");
		    s.add(t_before_27 >= (int)segLower + 1 && t_before_27 <= (int)segUpper && t_after_27 >= (int)segLower && t_after_27 <= (int)segUpper);
		    
		    func_decl rho_27 = function("rho_27", c.int_sort(), c.int_sort());
		    func_decl rho_primed_27 = function("rho_primed_27", c.real_sort(), c.real_sort());
		    
		    func_decl rho_72 = function("rho_72", c.int_sort(), c.int_sort());
		    func_decl rho_primed_72 = function("rho_primed_72", c.real_sort(), c.real_sort());
		    
		    expr pwl_27 = c.int_const("pwl_27");
		    s.add(pwl_27 >= (int)segLower + 1 && pwl_27 <= (int)segUpper);
		    
		    expr pwl_72 = c.int_const("pwl_72");
		    s.add(pwl_72 >= (int)segLower + 1 && pwl_72 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_27(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_27(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_72(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_72(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_27, t_after_27, implies(((t_before_27 < t_after_27) && (t_before_27 >= (int)segLower + 1) && (t_before_27 <= (int)segUpper) && (t_after_27 >= (int)segLower) && (t_after_27 <= (int)segUpper)), ((rho_27(t_before_27) < rho_27(t_after_27)) && (rho_72(t_before_27) < rho_72(t_after_27))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_7, implies(((rho_27(pred_2) == pred_7) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_2_x(pred_2)) * (a_7_x(pred_7) - a_2_x(pred_2))) + ((a_7_y(pred_7) - a_2_y(pred_2)) * (a_7_y(pred_7) - a_2_y(pred_2))) + ((a_7_z(pred_7) - a_2_z(pred_2)) * (a_7_z(pred_7) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_27, implies(((pwl_27 >= (int)segLower + 1) && (pwl_27 <= (int)segUpper)), (rho_primed_27(pwl_27) == rho_27(c.int_val(pwl_27)) + ((pwl_27 - c.int_val(pwl_27)) * (rho_27(c.int_val(pwl_27) + 1) - rho_27(c.int_val(pwl_27))))))));
			s.add(forall(pwl_72, implies(((pwl_72 >= (int)segLower + 1) && (pwl_72 <= (int)segUpper)), (rho_primed_72(pwl_72) == rho_72(c.int_val(pwl_72)) + ((pwl_72 - c.int_val(pwl_72)) * (rho_72(c.int_val(pwl_72) + 1) - rho_72(c.int_val(pwl_72))))))));
			
			//inverse re-timing
			s.add(forall(t_27, implies(((t_27 >= (int)segLower) && (t_27 <= (int)segUpper)), (rho_72(rho_27(t_27)) == t_27))));

			// ================ AGENT 2 AND AGENT 7 END ================ //
			
			// =============== AGENT 2 AND AGENT 8 START =============== //
			
			//agent pair smt variables
			expr t_28 = c.int_const("t_28");
		    s.add(t_28 >= (int)segLower + 1 && t_28 <= (int)segUpper);
		    
		    expr t_before_28 = c.int_const("t_before_28");
		    expr t_after_28 = c.int_const("t_after_28");
		    s.add(t_before_28 >= (int)segLower + 1 && t_before_28 <= (int)segUpper && t_after_28 >= (int)segLower && t_after_28 <= (int)segUpper);
		    
		    func_decl rho_28 = function("rho_28", c.int_sort(), c.int_sort());
		    func_decl rho_primed_28 = function("rho_primed_28", c.real_sort(), c.real_sort());
		    
		    func_decl rho_82 = function("rho_82", c.int_sort(), c.int_sort());
		    func_decl rho_primed_82 = function("rho_primed_82", c.real_sort(), c.real_sort());
		    
		    expr pwl_28 = c.int_const("pwl_28");
		    s.add(pwl_28 >= (int)segLower + 1 && pwl_28 <= (int)segUpper);
		    
		    expr pwl_82 = c.int_const("pwl_82");
		    s.add(pwl_82 >= (int)segLower + 1 && pwl_82 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_28(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_28(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_82(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_82(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_28, t_after_28, implies(((t_before_28 < t_after_28) && (t_before_28 >= (int)segLower + 1) && (t_before_28 <= (int)segUpper) && (t_after_28 >= (int)segLower) && (t_after_28 <= (int)segUpper)), ((rho_28(t_before_28) < rho_28(t_after_28)) && (rho_82(t_before_28) < rho_82(t_after_28))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_8, implies(((rho_28(pred_2) == pred_8) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_8 >= (int)segLower) && (pred_8 <= (int)segUpper)), (c.real_val(delta) <= (((a_8_x(pred_8) - a_2_x(pred_2)) * (a_8_x(pred_8) - a_2_x(pred_2))) + ((a_8_y(pred_8) - a_2_y(pred_2)) * (a_8_y(pred_8) - a_2_y(pred_2))) + ((a_8_z(pred_8) - a_2_z(pred_2)) * (a_8_z(pred_8) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_28, implies(((pwl_28 >= (int)segLower + 1) && (pwl_28 <= (int)segUpper)), (rho_primed_28(pwl_28) == rho_28(c.int_val(pwl_28)) + ((pwl_28 - c.int_val(pwl_28)) * (rho_28(c.int_val(pwl_28) + 1) - rho_28(c.int_val(pwl_28))))))));
			s.add(forall(pwl_82, implies(((pwl_82 >= (int)segLower + 1) && (pwl_82 <= (int)segUpper)), (rho_primed_82(pwl_82) == rho_82(c.int_val(pwl_82)) + ((pwl_82 - c.int_val(pwl_82)) * (rho_82(c.int_val(pwl_82) + 1) - rho_82(c.int_val(pwl_82))))))));
			
			//inverse re-timing
			s.add(forall(t_28, implies(((t_28 >= (int)segLower) && (t_28 <= (int)segUpper)), (rho_82(rho_28(t_28)) == t_28))));

			// ================ AGENT 2 AND AGENT 8 END ================ //
			
			// =============== AGENT 2 AND AGENT 9 START =============== //
			
			//agent pair smt variables
			expr t_29 = c.int_const("t_29");
		    s.add(t_29 >= (int)segLower + 1 && t_29 <= (int)segUpper);
		    
		    expr t_before_29 = c.int_const("t_before_29");
		    expr t_after_29 = c.int_const("t_after_29");
		    s.add(t_before_29 >= (int)segLower + 1 && t_before_29 <= (int)segUpper && t_after_29 >= (int)segLower && t_after_29 <= (int)segUpper);
		    
		    func_decl rho_29 = function("rho_29", c.int_sort(), c.int_sort());
		    func_decl rho_primed_29 = function("rho_primed_29", c.real_sort(), c.real_sort());
		    
		    func_decl rho_92 = function("rho_92", c.int_sort(), c.int_sort());
		    func_decl rho_primed_92 = function("rho_primed_92", c.real_sort(), c.real_sort());
		    
		    expr pwl_29 = c.int_const("pwl_29");
		    s.add(pwl_29 >= (int)segLower + 1 && pwl_29 <= (int)segUpper);
		    
		    expr pwl_92 = c.int_const("pwl_92");
		    s.add(pwl_92 >= (int)segLower + 1 && pwl_92 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_29(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_29(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_92(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_92(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_29, t_after_29, implies(((t_before_29 < t_after_29) && (t_before_29 >= (int)segLower + 1) && (t_before_29 <= (int)segUpper) && (t_after_29 >= (int)segLower) && (t_after_29 <= (int)segUpper)), ((rho_29(t_before_29) < rho_29(t_after_29)) && (rho_92(t_before_29) < rho_92(t_after_29))))));
			
			//mutual separation constraint
			s.add(forall(pred_2, pred_9, implies(((rho_29(pred_2) == pred_9) && (pred_2 >= (int)segLower + 1) && (pred_2 <= (int)segUpper) && (pred_9 >= (int)segLower) && (pred_9 <= (int)segUpper)), (c.real_val(delta) <= (((a_9_x(pred_9) - a_2_x(pred_2)) * (a_9_x(pred_9) - a_2_x(pred_2))) + ((a_9_y(pred_9) - a_2_y(pred_2)) * (a_9_y(pred_9) - a_2_y(pred_2))) + ((a_9_z(pred_9) - a_2_z(pred_2)) * (a_9_z(pred_9) - a_2_z(pred_2))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_29, implies(((pwl_29 >= (int)segLower + 1) && (pwl_29 <= (int)segUpper)), (rho_primed_29(pwl_29) == rho_29(c.int_val(pwl_29)) + ((pwl_29 - c.int_val(pwl_29)) * (rho_29(c.int_val(pwl_29) + 1) - rho_29(c.int_val(pwl_29))))))));
			s.add(forall(pwl_92, implies(((pwl_92 >= (int)segLower + 1) && (pwl_92 <= (int)segUpper)), (rho_primed_92(pwl_92) == rho_92(c.int_val(pwl_92)) + ((pwl_92 - c.int_val(pwl_92)) * (rho_92(c.int_val(pwl_92) + 1) - rho_92(c.int_val(pwl_92))))))));
			
			//inverse re-timing
			s.add(forall(t_29, implies(((t_29 >= (int)segLower) && (t_29 <= (int)segUpper)), (rho_92(rho_29(t_29)) == t_29))));

			// ================ AGENT 2 AND AGENT 9 END ================ //
			
			// =============== AGENT 3 AND AGENT 4 START =============== //
			
			//agent pair smt variables
			expr t_34 = c.int_const("t_34");
		    s.add(t_34 >= (int)segLower + 1 && t_34 <= (int)segUpper);
		    
		    expr t_before_34 = c.int_const("t_before_34");
		    expr t_after_34 = c.int_const("t_after_34");
		    s.add(t_before_34 >= (int)segLower + 1 && t_before_34 <= (int)segUpper && t_after_34 >= (int)segLower && t_after_34 <= (int)segUpper);
		    
		    func_decl rho_34 = function("rho_34", c.int_sort(), c.int_sort());
		    func_decl rho_primed_34 = function("rho_primed_34", c.real_sort(), c.real_sort());
		    
		    func_decl rho_43 = function("rho_43", c.int_sort(), c.int_sort());
		    func_decl rho_primed_43 = function("rho_primed_43", c.real_sort(), c.real_sort());
		    
		    expr pwl_34 = c.int_const("pwl_34");
		    s.add(pwl_34 >= (int)segLower + 1 && pwl_34 <= (int)segUpper);
		    
		    expr pwl_43 = c.int_const("pwl_43");
		    s.add(pwl_43 >= (int)segLower + 1 && pwl_43 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_34(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_34(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_43(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_43(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_34, t_after_34, implies(((t_before_34 < t_after_34) && (t_before_34 >= (int)segLower + 1) && (t_before_34 <= (int)segUpper) && (t_after_34 >= (int)segLower) && (t_after_34 <= (int)segUpper)), ((rho_34(t_before_34) < rho_34(t_after_34)) && (rho_43(t_before_34) < rho_43(t_after_34))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_4, implies(((rho_34(pred_3) == pred_4) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_4 >= (int)segLower) && (pred_4 <= (int)segUpper)), (c.real_val(delta) <= (((a_4_x(pred_4) - a_3_x(pred_3)) * (a_4_x(pred_4) - a_3_x(pred_3))) + ((a_4_y(pred_4) - a_3_y(pred_3)) * (a_4_y(pred_4) - a_3_y(pred_3))) + ((a_4_z(pred_4) - a_3_z(pred_3)) * (a_4_z(pred_4) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_34, implies(((pwl_34 >= (int)segLower + 1) && (pwl_34 <= (int)segUpper)), (rho_primed_34(pwl_34) == rho_34(c.int_val(pwl_34)) + ((pwl_34 - c.int_val(pwl_34)) * (rho_34(c.int_val(pwl_34) + 1) - rho_34(c.int_val(pwl_34))))))));
			s.add(forall(pwl_43, implies(((pwl_43 >= (int)segLower + 1) && (pwl_43 <= (int)segUpper)), (rho_primed_43(pwl_43) == rho_43(c.int_val(pwl_43)) + ((pwl_43 - c.int_val(pwl_43)) * (rho_43(c.int_val(pwl_43) + 1) - rho_43(c.int_val(pwl_43))))))));
			
			//inverse re-timing
			s.add(forall(t_34, implies(((t_34 >= (int)segLower) && (t_34 <= (int)segUpper)), (rho_43(rho_34(t_34)) == t_34))));

			// ================ AGENT 3 AND AGENT 4 END ================ //
			
			// =============== AGENT 3 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_35 = c.int_const("t_35");
		    s.add(t_35 >= (int)segLower + 1 && t_35 <= (int)segUpper);
		    
		    expr t_before_35 = c.int_const("t_before_35");
		    expr t_after_35 = c.int_const("t_after_35");
		    s.add(t_before_35 >= (int)segLower + 1 && t_before_35 <= (int)segUpper && t_after_35 >= (int)segLower && t_after_35 <= (int)segUpper);
		    
		    func_decl rho_35 = function("rho_35", c.int_sort(), c.int_sort());
		    func_decl rho_primed_35 = function("rho_primed_35", c.real_sort(), c.real_sort());
		    
		    func_decl rho_53 = function("rho_53", c.int_sort(), c.int_sort());
		    func_decl rho_primed_53 = function("rho_primed_53", c.real_sort(), c.real_sort());
		    
		    expr pwl_35 = c.int_const("pwl_35");
		    s.add(pwl_35 >= (int)segLower + 1 && pwl_35 <= (int)segUpper);
		    
		    expr pwl_53 = c.int_const("pwl_53");
		    s.add(pwl_53 >= (int)segLower + 1 && pwl_53 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_35(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_35(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_53(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_53(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_35, t_after_35, implies(((t_before_35 < t_after_35) && (t_before_35 >= (int)segLower + 1) && (t_before_35 <= (int)segUpper) && (t_after_35 >= (int)segLower) && (t_after_35 <= (int)segUpper)), ((rho_35(t_before_35) < rho_35(t_after_35)) && (rho_53(t_before_35) < rho_53(t_after_35))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_5, implies(((rho_35(pred_3) == pred_5) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_3_x(pred_3)) * (a_5_x(pred_5) - a_3_x(pred_3))) + ((a_5_y(pred_5) - a_3_y(pred_3)) * (a_5_y(pred_5) - a_3_y(pred_3))) + ((a_5_z(pred_5) - a_3_z(pred_3)) * (a_5_z(pred_5) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_35, implies(((pwl_35 >= (int)segLower + 1) && (pwl_35 <= (int)segUpper)), (rho_primed_35(pwl_35) == rho_35(c.int_val(pwl_35)) + ((pwl_35 - c.int_val(pwl_35)) * (rho_35(c.int_val(pwl_35) + 1) - rho_35(c.int_val(pwl_35))))))));
			s.add(forall(pwl_53, implies(((pwl_53 >= (int)segLower + 1) && (pwl_53 <= (int)segUpper)), (rho_primed_53(pwl_53) == rho_53(c.int_val(pwl_53)) + ((pwl_53 - c.int_val(pwl_53)) * (rho_53(c.int_val(pwl_53) + 1) - rho_53(c.int_val(pwl_53))))))));
			
			//inverse re-timing
			s.add(forall(t_35, implies(((t_35 >= (int)segLower) && (t_35 <= (int)segUpper)), (rho_53(rho_35(t_35)) == t_35))));

			// ================ AGENT 3 AND AGENT 5 END ================ //
			
			// =============== AGENT 3 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_36 = c.int_const("t_36");
		    s.add(t_36 >= (int)segLower + 1 && t_36 <= (int)segUpper);
		    
		    expr t_before_36 = c.int_const("t_before_36");
		    expr t_after_36 = c.int_const("t_after_36");
		    s.add(t_before_36 >= (int)segLower + 1 && t_before_36 <= (int)segUpper && t_after_36 >= (int)segLower && t_after_36 <= (int)segUpper);
		    
		    func_decl rho_36 = function("rho_36", c.int_sort(), c.int_sort());
		    func_decl rho_primed_36 = function("rho_primed_36", c.real_sort(), c.real_sort());
		    
		    func_decl rho_63 = function("rho_63", c.int_sort(), c.int_sort());
		    func_decl rho_primed_63 = function("rho_primed_63", c.real_sort(), c.real_sort());
		    
		    expr pwl_36 = c.int_const("pwl_36");
		    s.add(pwl_36 >= (int)segLower + 1 && pwl_36 <= (int)segUpper);
		    
		    expr pwl_63 = c.int_const("pwl_63");
		    s.add(pwl_63 >= (int)segLower + 1 && pwl_63 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_36(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_36(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_63(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_63(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_36, t_after_36, implies(((t_before_36 < t_after_36) && (t_before_36 >= (int)segLower + 1) && (t_before_36 <= (int)segUpper) && (t_after_36 >= (int)segLower) && (t_after_36 <= (int)segUpper)), ((rho_36(t_before_36) < rho_36(t_after_36)) && (rho_63(t_before_36) < rho_63(t_after_36))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_6, implies(((rho_36(pred_3) == pred_6) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_3_x(pred_3)) * (a_6_x(pred_6) - a_3_x(pred_3))) + ((a_6_y(pred_6) - a_3_y(pred_3)) * (a_6_y(pred_6) - a_3_y(pred_3))) + ((a_6_z(pred_6) - a_3_z(pred_3)) * (a_6_z(pred_6) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_36, implies(((pwl_36 >= (int)segLower + 1) && (pwl_36 <= (int)segUpper)), (rho_primed_36(pwl_36) == rho_36(c.int_val(pwl_36)) + ((pwl_36 - c.int_val(pwl_36)) * (rho_36(c.int_val(pwl_36) + 1) - rho_36(c.int_val(pwl_36))))))));
			s.add(forall(pwl_63, implies(((pwl_63 >= (int)segLower + 1) && (pwl_63 <= (int)segUpper)), (rho_primed_63(pwl_63) == rho_63(c.int_val(pwl_63)) + ((pwl_63 - c.int_val(pwl_63)) * (rho_63(c.int_val(pwl_63) + 1) - rho_63(c.int_val(pwl_63))))))));
			
			//inverse re-timing
			s.add(forall(t_36, implies(((t_36 >= (int)segLower) && (t_36 <= (int)segUpper)), (rho_63(rho_36(t_36)) == t_36))));

			// ================ AGENT 3 AND AGENT 6 END ================ //
			
			// =============== AGENT 3 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_37 = c.int_const("t_37");
		    s.add(t_37 >= (int)segLower + 1 && t_37 <= (int)segUpper);
		    
		    expr t_before_37 = c.int_const("t_before_37");
		    expr t_after_37 = c.int_const("t_after_37");
		    s.add(t_before_37 >= (int)segLower + 1 && t_before_37 <= (int)segUpper && t_after_37 >= (int)segLower && t_after_37 <= (int)segUpper);
		    
		    func_decl rho_37 = function("rho_37", c.int_sort(), c.int_sort());
		    func_decl rho_primed_37 = function("rho_primed_37", c.real_sort(), c.real_sort());
		    
		    func_decl rho_73 = function("rho_73", c.int_sort(), c.int_sort());
		    func_decl rho_primed_73 = function("rho_primed_73", c.real_sort(), c.real_sort());
		    
		    expr pwl_37 = c.int_const("pwl_37");
		    s.add(pwl_37 >= (int)segLower + 1 && pwl_37 <= (int)segUpper);
		    
		    expr pwl_73 = c.int_const("pwl_73");
		    s.add(pwl_73 >= (int)segLower + 1 && pwl_73 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_37(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_37(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_73(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_73(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_37, t_after_37, implies(((t_before_37 < t_after_37) && (t_before_37 >= (int)segLower + 1) && (t_before_37 <= (int)segUpper) && (t_after_37 >= (int)segLower) && (t_after_37 <= (int)segUpper)), ((rho_37(t_before_37) < rho_37(t_after_37)) && (rho_73(t_before_37) < rho_73(t_after_37))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_7, implies(((rho_37(pred_3) == pred_7) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_3_x(pred_3)) * (a_7_x(pred_7) - a_3_x(pred_3))) + ((a_7_y(pred_7) - a_3_y(pred_3)) * (a_7_y(pred_7) - a_3_y(pred_3))) + ((a_7_z(pred_7) - a_3_z(pred_3)) * (a_7_z(pred_7) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_37, implies(((pwl_37 >= (int)segLower + 1) && (pwl_37 <= (int)segUpper)), (rho_primed_37(pwl_37) == rho_37(c.int_val(pwl_37)) + ((pwl_37 - c.int_val(pwl_37)) * (rho_37(c.int_val(pwl_37) + 1) - rho_37(c.int_val(pwl_37))))))));
			s.add(forall(pwl_73, implies(((pwl_73 >= (int)segLower + 1) && (pwl_73 <= (int)segUpper)), (rho_primed_73(pwl_73) == rho_73(c.int_val(pwl_73)) + ((pwl_73 - c.int_val(pwl_73)) * (rho_73(c.int_val(pwl_73) + 1) - rho_73(c.int_val(pwl_73))))))));
			
			//inverse re-timing
			s.add(forall(t_37, implies(((t_37 >= (int)segLower) && (t_37 <= (int)segUpper)), (rho_73(rho_37(t_37)) == t_37))));

			// ================ AGENT 3 AND AGENT 7 END ================ //
			
			// =============== AGENT 3 AND AGENT 8 START =============== //
			
			//agent pair smt variables
			expr t_38 = c.int_const("t_38");
		    s.add(t_38 >= (int)segLower + 1 && t_38 <= (int)segUpper);
		    
		    expr t_before_38 = c.int_const("t_before_38");
		    expr t_after_38 = c.int_const("t_after_38");
		    s.add(t_before_38 >= (int)segLower + 1 && t_before_38 <= (int)segUpper && t_after_38 >= (int)segLower && t_after_38 <= (int)segUpper);
		    
		    func_decl rho_38 = function("rho_38", c.int_sort(), c.int_sort());
		    func_decl rho_primed_38 = function("rho_primed_38", c.real_sort(), c.real_sort());
		    
		    func_decl rho_83 = function("rho_83", c.int_sort(), c.int_sort());
		    func_decl rho_primed_83 = function("rho_primed_83", c.real_sort(), c.real_sort());
		    
		    expr pwl_38 = c.int_const("pwl_38");
		    s.add(pwl_38 >= (int)segLower + 1 && pwl_38 <= (int)segUpper);
		    
		    expr pwl_83 = c.int_const("pwl_83");
		    s.add(pwl_83 >= (int)segLower + 1 && pwl_83 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_38(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_38(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_83(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_83(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_38, t_after_38, implies(((t_before_38 < t_after_38) && (t_before_38 >= (int)segLower + 1) && (t_before_38 <= (int)segUpper) && (t_after_38 >= (int)segLower) && (t_after_38 <= (int)segUpper)), ((rho_38(t_before_38) < rho_38(t_after_38)) && (rho_83(t_before_38) < rho_83(t_after_38))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_8, implies(((rho_38(pred_3) == pred_8) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_8 >= (int)segLower) && (pred_8 <= (int)segUpper)), (c.real_val(delta) <= (((a_8_x(pred_8) - a_3_x(pred_3)) * (a_8_x(pred_8) - a_3_x(pred_3))) + ((a_8_y(pred_8) - a_3_y(pred_3)) * (a_8_y(pred_8) - a_3_y(pred_3))) + ((a_8_z(pred_8) - a_3_z(pred_3)) * (a_8_z(pred_8) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_38, implies(((pwl_38 >= (int)segLower + 1) && (pwl_38 <= (int)segUpper)), (rho_primed_38(pwl_38) == rho_38(c.int_val(pwl_38)) + ((pwl_38 - c.int_val(pwl_38)) * (rho_38(c.int_val(pwl_38) + 1) - rho_38(c.int_val(pwl_38))))))));
			s.add(forall(pwl_83, implies(((pwl_83 >= (int)segLower + 1) && (pwl_83 <= (int)segUpper)), (rho_primed_83(pwl_83) == rho_83(c.int_val(pwl_83)) + ((pwl_83 - c.int_val(pwl_83)) * (rho_83(c.int_val(pwl_83) + 1) - rho_83(c.int_val(pwl_83))))))));
			
			//inverse re-timing
			s.add(forall(t_38, implies(((t_38 >= (int)segLower) && (t_38 <= (int)segUpper)), (rho_83(rho_38(t_38)) == t_38))));

			// ================ AGENT 3 AND AGENT 8 END ================ //
			
			// =============== AGENT 3 AND AGENT 9 START =============== //
			
			//agent pair smt variables
			expr t_39 = c.int_const("t_39");
		    s.add(t_39 >= (int)segLower + 1 && t_39 <= (int)segUpper);
		    
		    expr t_before_39 = c.int_const("t_before_39");
		    expr t_after_39 = c.int_const("t_after_39");
		    s.add(t_before_39 >= (int)segLower + 1 && t_before_39 <= (int)segUpper && t_after_39 >= (int)segLower && t_after_39 <= (int)segUpper);
		    
		    func_decl rho_39 = function("rho_39", c.int_sort(), c.int_sort());
		    func_decl rho_primed_39 = function("rho_primed_39", c.real_sort(), c.real_sort());
		    
		    func_decl rho_93 = function("rho_93", c.int_sort(), c.int_sort());
		    func_decl rho_primed_93 = function("rho_primed_93", c.real_sort(), c.real_sort());
		    
		    expr pwl_39 = c.int_const("pwl_39");
		    s.add(pwl_39 >= (int)segLower + 1 && pwl_39 <= (int)segUpper);
		    
		    expr pwl_93 = c.int_const("pwl_93");
		    s.add(pwl_93 >= (int)segLower + 1 && pwl_93 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_39(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_39(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_93(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_93(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_39, t_after_39, implies(((t_before_39 < t_after_39) && (t_before_39 >= (int)segLower + 1) && (t_before_39 <= (int)segUpper) && (t_after_39 >= (int)segLower) && (t_after_39 <= (int)segUpper)), ((rho_39(t_before_39) < rho_39(t_after_39)) && (rho_93(t_before_39) < rho_93(t_after_39))))));
			
			//mutual separation constraint
			s.add(forall(pred_3, pred_9, implies(((rho_39(pred_3) == pred_9) && (pred_3 >= (int)segLower + 1) && (pred_3 <= (int)segUpper) && (pred_9 >= (int)segLower) && (pred_9 <= (int)segUpper)), (c.real_val(delta) <= (((a_9_x(pred_9) - a_3_x(pred_3)) * (a_9_x(pred_9) - a_3_x(pred_3))) + ((a_9_y(pred_9) - a_3_y(pred_3)) * (a_9_y(pred_9) - a_3_y(pred_3))) + ((a_9_z(pred_9) - a_3_z(pred_3)) * (a_9_z(pred_9) - a_3_z(pred_3))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_39, implies(((pwl_39 >= (int)segLower + 1) && (pwl_39 <= (int)segUpper)), (rho_primed_39(pwl_39) == rho_39(c.int_val(pwl_39)) + ((pwl_39 - c.int_val(pwl_39)) * (rho_39(c.int_val(pwl_39) + 1) - rho_39(c.int_val(pwl_39))))))));
			s.add(forall(pwl_93, implies(((pwl_93 >= (int)segLower + 1) && (pwl_93 <= (int)segUpper)), (rho_primed_93(pwl_93) == rho_93(c.int_val(pwl_93)) + ((pwl_93 - c.int_val(pwl_93)) * (rho_93(c.int_val(pwl_93) + 1) - rho_93(c.int_val(pwl_93))))))));
			
			//inverse re-timing
			s.add(forall(t_39, implies(((t_39 >= (int)segLower) && (t_39 <= (int)segUpper)), (rho_93(rho_39(t_39)) == t_39))));

			// ================ AGENT 3 AND AGENT 9 END ================ //
			
			// =============== AGENT 4 AND AGENT 5 START =============== //
			
			//agent pair smt variables
			expr t_45 = c.int_const("t_45");
		    s.add(t_45 >= (int)segLower + 1 && t_45 <= (int)segUpper);
		    
		    expr t_before_45 = c.int_const("t_before_45");
		    expr t_after_45 = c.int_const("t_after_45");
		    s.add(t_before_45 >= (int)segLower + 1 && t_before_45 <= (int)segUpper && t_after_45 >= (int)segLower && t_after_45 <= (int)segUpper);
		    
		    func_decl rho_45 = function("rho_45", c.int_sort(), c.int_sort());
		    func_decl rho_primed_45 = function("rho_primed_45", c.real_sort(), c.real_sort());
		    
		    func_decl rho_54 = function("rho_54", c.int_sort(), c.int_sort());
		    func_decl rho_primed_54 = function("rho_primed_54", c.real_sort(), c.real_sort());
		    
		    expr pwl_45 = c.int_const("pwl_45");
		    s.add(pwl_45 >= (int)segLower + 1 && pwl_45 <= (int)segUpper);
		    
		    expr pwl_54 = c.int_const("pwl_54");
		    s.add(pwl_54 >= (int)segLower + 1 && pwl_54 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_45(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_45(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_54(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_54(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_45, t_after_45, implies(((t_before_45 < t_after_45) && (t_before_45 >= (int)segLower + 1) && (t_before_45 <= (int)segUpper) && (t_after_45 >= (int)segLower) && (t_after_45 <= (int)segUpper)), ((rho_45(t_before_45) < rho_45(t_after_45)) && (rho_54(t_before_45) < rho_54(t_after_45))))));
			
			//mutual separation constraint
			s.add(forall(pred_4, pred_5, implies(((rho_45(pred_4) == pred_5) && (pred_4 >= (int)segLower + 1) && (pred_4 <= (int)segUpper) && (pred_5 >= (int)segLower) && (pred_5 <= (int)segUpper)), (c.real_val(delta) <= (((a_5_x(pred_5) - a_4_x(pred_4)) * (a_5_x(pred_5) - a_4_x(pred_4))) + ((a_5_y(pred_5) - a_4_y(pred_4)) * (a_5_y(pred_5) - a_4_y(pred_4))) + ((a_5_z(pred_5) - a_4_z(pred_4)) * (a_5_z(pred_5) - a_4_z(pred_4))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_45, implies(((pwl_45 >= (int)segLower + 1) && (pwl_45 <= (int)segUpper)), (rho_primed_45(pwl_45) == rho_45(c.int_val(pwl_45)) + ((pwl_45 - c.int_val(pwl_45)) * (rho_45(c.int_val(pwl_45) + 1) - rho_45(c.int_val(pwl_45))))))));
			s.add(forall(pwl_54, implies(((pwl_54 >= (int)segLower + 1) && (pwl_54 <= (int)segUpper)), (rho_primed_54(pwl_54) == rho_54(c.int_val(pwl_54)) + ((pwl_54 - c.int_val(pwl_54)) * (rho_54(c.int_val(pwl_54) + 1) - rho_54(c.int_val(pwl_54))))))));
			
			//inverse re-timing
			s.add(forall(t_45, implies(((t_45 >= (int)segLower) && (t_45 <= (int)segUpper)), (rho_54(rho_45(t_45)) == t_45))));

			// ================ AGENT 4 AND AGENT 5 END ================ //
			
			// =============== AGENT 4 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_46 = c.int_const("t_46");
		    s.add(t_46 >= (int)segLower + 1 && t_46 <= (int)segUpper);
		    
		    expr t_before_46 = c.int_const("t_before_46");
		    expr t_after_46 = c.int_const("t_after_46");
		    s.add(t_before_46 >= (int)segLower + 1 && t_before_46 <= (int)segUpper && t_after_46 >= (int)segLower && t_after_46 <= (int)segUpper);
		    
		    func_decl rho_46 = function("rho_46", c.int_sort(), c.int_sort());
		    func_decl rho_primed_46 = function("rho_primed_46", c.real_sort(), c.real_sort());
		    
		    func_decl rho_64 = function("rho_64", c.int_sort(), c.int_sort());
		    func_decl rho_primed_64 = function("rho_primed_64", c.real_sort(), c.real_sort());
		    
		    expr pwl_46 = c.int_const("pwl_46");
		    s.add(pwl_46 >= (int)segLower + 1 && pwl_46 <= (int)segUpper);
		    
		    expr pwl_64 = c.int_const("pwl_64");
		    s.add(pwl_64 >= (int)segLower + 1 && pwl_64 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_46(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_46(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_64(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_64(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_46, t_after_46, implies(((t_before_46 < t_after_46) && (t_before_46 >= (int)segLower + 1) && (t_before_46 <= (int)segUpper) && (t_after_46 >= (int)segLower) && (t_after_46 <= (int)segUpper)), ((rho_46(t_before_46) < rho_46(t_after_46)) && (rho_64(t_before_46) < rho_64(t_after_46))))));
			
			//mutual separation constraint
			s.add(forall(pred_4, pred_6, implies(((rho_46(pred_4) == pred_6) && (pred_4 >= (int)segLower + 1) && (pred_4 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_4_x(pred_4)) * (a_6_x(pred_6) - a_4_x(pred_4))) + ((a_6_y(pred_6) - a_4_y(pred_4)) * (a_6_y(pred_6) - a_4_y(pred_4))) + ((a_6_z(pred_6) - a_4_z(pred_4)) * (a_6_z(pred_6) - a_4_z(pred_4))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_46, implies(((pwl_46 >= (int)segLower + 1) && (pwl_46 <= (int)segUpper)), (rho_primed_46(pwl_46) == rho_46(c.int_val(pwl_46)) + ((pwl_46 - c.int_val(pwl_46)) * (rho_46(c.int_val(pwl_46) + 1) - rho_46(c.int_val(pwl_46))))))));
			s.add(forall(pwl_64, implies(((pwl_64 >= (int)segLower + 1) && (pwl_64 <= (int)segUpper)), (rho_primed_64(pwl_64) == rho_64(c.int_val(pwl_64)) + ((pwl_64 - c.int_val(pwl_64)) * (rho_64(c.int_val(pwl_64) + 1) - rho_64(c.int_val(pwl_64))))))));
			
			//inverse re-timing
			s.add(forall(t_46, implies(((t_46 >= (int)segLower) && (t_46 <= (int)segUpper)), (rho_64(rho_46(t_46)) == t_46))));

			// ================ AGENT 4 AND AGENT 6 END ================ //
			
			// =============== AGENT 4 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_47 = c.int_const("t_47");
		    s.add(t_47 >= (int)segLower + 1 && t_47 <= (int)segUpper);
		    
		    expr t_before_47 = c.int_const("t_before_47");
		    expr t_after_47 = c.int_const("t_after_47");
		    s.add(t_before_47 >= (int)segLower + 1 && t_before_47 <= (int)segUpper && t_after_47 >= (int)segLower && t_after_47 <= (int)segUpper);
		    
		    func_decl rho_47 = function("rho_47", c.int_sort(), c.int_sort());
		    func_decl rho_primed_47 = function("rho_primed_47", c.real_sort(), c.real_sort());
		    
		    func_decl rho_74 = function("rho_74", c.int_sort(), c.int_sort());
		    func_decl rho_primed_74 = function("rho_primed_74", c.real_sort(), c.real_sort());
		    
		    expr pwl_47 = c.int_const("pwl_47");
		    s.add(pwl_47 >= (int)segLower + 1 && pwl_47 <= (int)segUpper);
		    
		    expr pwl_74 = c.int_const("pwl_74");
		    s.add(pwl_74 >= (int)segLower + 1 && pwl_74 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_47(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_47(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_74(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_74(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_47, t_after_47, implies(((t_before_47 < t_after_47) && (t_before_47 >= (int)segLower + 1) && (t_before_47 <= (int)segUpper) && (t_after_47 >= (int)segLower) && (t_after_47 <= (int)segUpper)), ((rho_47(t_before_47) < rho_47(t_after_47)) && (rho_74(t_before_47) < rho_74(t_after_47))))));
			
			//mutual separation constraint
			s.add(forall(pred_4, pred_7, implies(((rho_47(pred_4) == pred_7) && (pred_4 >= (int)segLower + 1) && (pred_4 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_4_x(pred_4)) * (a_7_x(pred_7) - a_4_x(pred_4))) + ((a_7_y(pred_7) - a_4_y(pred_4)) * (a_7_y(pred_7) - a_4_y(pred_4))) + ((a_7_z(pred_7) - a_4_z(pred_4)) * (a_7_z(pred_7) - a_4_z(pred_4))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_47, implies(((pwl_47 >= (int)segLower + 1) && (pwl_47 <= (int)segUpper)), (rho_primed_47(pwl_47) == rho_47(c.int_val(pwl_47)) + ((pwl_47 - c.int_val(pwl_47)) * (rho_47(c.int_val(pwl_47) + 1) - rho_47(c.int_val(pwl_47))))))));
			s.add(forall(pwl_74, implies(((pwl_74 >= (int)segLower + 1) && (pwl_74 <= (int)segUpper)), (rho_primed_74(pwl_74) == rho_74(c.int_val(pwl_74)) + ((pwl_74 - c.int_val(pwl_74)) * (rho_74(c.int_val(pwl_74) + 1) - rho_74(c.int_val(pwl_74))))))));
			
			//inverse re-timing
			s.add(forall(t_47, implies(((t_47 >= (int)segLower) && (t_47 <= (int)segUpper)), (rho_74(rho_47(t_47)) == t_47))));

			// ================ AGENT 4 AND AGENT 7 END ================ //
			
			// =============== AGENT 4 AND AGENT 8 START =============== //
			
			//agent pair smt variables
			expr t_48 = c.int_const("t_48");
		    s.add(t_48 >= (int)segLower + 1 && t_48 <= (int)segUpper);
		    
		    expr t_before_48 = c.int_const("t_before_48");
		    expr t_after_48 = c.int_const("t_after_48");
		    s.add(t_before_48 >= (int)segLower + 1 && t_before_48 <= (int)segUpper && t_after_48 >= (int)segLower && t_after_48 <= (int)segUpper);
		    
		    func_decl rho_48 = function("rho_48", c.int_sort(), c.int_sort());
		    func_decl rho_primed_48 = function("rho_primed_48", c.real_sort(), c.real_sort());
		    
		    func_decl rho_84 = function("rho_84", c.int_sort(), c.int_sort());
		    func_decl rho_primed_84 = function("rho_primed_84", c.real_sort(), c.real_sort());
		    
		    expr pwl_48 = c.int_const("pwl_48");
		    s.add(pwl_48 >= (int)segLower + 1 && pwl_48 <= (int)segUpper);
		    
		    expr pwl_84 = c.int_const("pwl_84");
		    s.add(pwl_84 >= (int)segLower + 1 && pwl_84 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_48(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_48(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_84(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_84(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_48, t_after_48, implies(((t_before_48 < t_after_48) && (t_before_48 >= (int)segLower + 1) && (t_before_48 <= (int)segUpper) && (t_after_48 >= (int)segLower) && (t_after_48 <= (int)segUpper)), ((rho_48(t_before_48) < rho_48(t_after_48)) && (rho_84(t_before_48) < rho_84(t_after_48))))));
			
			//mutual separation constraint
			s.add(forall(pred_4, pred_8, implies(((rho_48(pred_4) == pred_8) && (pred_4 >= (int)segLower + 1) && (pred_4 <= (int)segUpper) && (pred_8 >= (int)segLower) && (pred_8 <= (int)segUpper)), (c.real_val(delta) <= (((a_8_x(pred_8) - a_4_x(pred_4)) * (a_8_x(pred_8) - a_4_x(pred_4))) + ((a_8_y(pred_8) - a_4_y(pred_4)) * (a_8_y(pred_8) - a_4_y(pred_4))) + ((a_8_z(pred_8) - a_4_z(pred_4)) * (a_8_z(pred_8) - a_4_z(pred_4))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_48, implies(((pwl_48 >= (int)segLower + 1) && (pwl_48 <= (int)segUpper)), (rho_primed_48(pwl_48) == rho_48(c.int_val(pwl_48)) + ((pwl_48 - c.int_val(pwl_48)) * (rho_48(c.int_val(pwl_48) + 1) - rho_48(c.int_val(pwl_48))))))));
			s.add(forall(pwl_84, implies(((pwl_84 >= (int)segLower + 1) && (pwl_84 <= (int)segUpper)), (rho_primed_84(pwl_84) == rho_84(c.int_val(pwl_84)) + ((pwl_84 - c.int_val(pwl_84)) * (rho_84(c.int_val(pwl_84) + 1) - rho_84(c.int_val(pwl_84))))))));
			
			//inverse re-timing
			s.add(forall(t_48, implies(((t_48 >= (int)segLower) && (t_48 <= (int)segUpper)), (rho_84(rho_48(t_48)) == t_48))));

			// ================ AGENT 4 AND AGENT 8 END ================ //
			
			// =============== AGENT 4 AND AGENT 9 START =============== //
			
			//agent pair smt variables
			expr t_49 = c.int_const("t_49");
		    s.add(t_49 >= (int)segLower + 1 && t_49 <= (int)segUpper);
		    
		    expr t_before_49 = c.int_const("t_before_49");
		    expr t_after_49 = c.int_const("t_after_49");
		    s.add(t_before_49 >= (int)segLower + 1 && t_before_49 <= (int)segUpper && t_after_49 >= (int)segLower && t_after_49 <= (int)segUpper);
		    
		    func_decl rho_49 = function("rho_49", c.int_sort(), c.int_sort());
		    func_decl rho_primed_49 = function("rho_primed_49", c.real_sort(), c.real_sort());
		    
		    func_decl rho_94 = function("rho_94", c.int_sort(), c.int_sort());
		    func_decl rho_primed_94 = function("rho_primed_94", c.real_sort(), c.real_sort());
		    
		    expr pwl_49 = c.int_const("pwl_49");
		    s.add(pwl_49 >= (int)segLower + 1 && pwl_49 <= (int)segUpper);
		    
		    expr pwl_94 = c.int_const("pwl_94");
		    s.add(pwl_94 >= (int)segLower + 1 && pwl_94 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_49(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_49(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_94(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_94(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_49, t_after_49, implies(((t_before_49 < t_after_49) && (t_before_49 >= (int)segLower + 1) && (t_before_49 <= (int)segUpper) && (t_after_49 >= (int)segLower) && (t_after_49 <= (int)segUpper)), ((rho_49(t_before_49) < rho_49(t_after_49)) && (rho_94(t_before_49) < rho_94(t_after_49))))));
			
			//mutual separation constraint
			s.add(forall(pred_4, pred_9, implies(((rho_49(pred_4) == pred_9) && (pred_4 >= (int)segLower + 1) && (pred_4 <= (int)segUpper) && (pred_9 >= (int)segLower) && (pred_9 <= (int)segUpper)), (c.real_val(delta) <= (((a_9_x(pred_9) - a_4_x(pred_4)) * (a_9_x(pred_9) - a_4_x(pred_4))) + ((a_9_y(pred_9) - a_4_y(pred_4)) * (a_9_y(pred_9) - a_4_y(pred_4))) + ((a_9_z(pred_9) - a_4_z(pred_4)) * (a_9_z(pred_9) - a_4_z(pred_4))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_49, implies(((pwl_49 >= (int)segLower + 1) && (pwl_49 <= (int)segUpper)), (rho_primed_49(pwl_49) == rho_49(c.int_val(pwl_49)) + ((pwl_49 - c.int_val(pwl_49)) * (rho_49(c.int_val(pwl_49) + 1) - rho_49(c.int_val(pwl_49))))))));
			s.add(forall(pwl_94, implies(((pwl_94 >= (int)segLower + 1) && (pwl_94 <= (int)segUpper)), (rho_primed_94(pwl_94) == rho_94(c.int_val(pwl_94)) + ((pwl_94 - c.int_val(pwl_94)) * (rho_94(c.int_val(pwl_94) + 1) - rho_94(c.int_val(pwl_94))))))));
			
			//inverse re-timing
			s.add(forall(t_49, implies(((t_49 >= (int)segLower) && (t_49 <= (int)segUpper)), (rho_94(rho_49(t_49)) == t_49))));

			// ================ AGENT 4 AND AGENT 9 END ================ //
			
			// =============== AGENT 5 AND AGENT 6 START =============== //
			
			//agent pair smt variables
			expr t_56 = c.int_const("t_56");
		    s.add(t_56 >= (int)segLower + 1 && t_56 <= (int)segUpper);
		    
		    expr t_before_56 = c.int_const("t_before_56");
		    expr t_after_56 = c.int_const("t_after_56");
		    s.add(t_before_56 >= (int)segLower + 1 && t_before_56 <= (int)segUpper && t_after_56 >= (int)segLower && t_after_56 <= (int)segUpper);
		    
		    func_decl rho_56 = function("rho_56", c.int_sort(), c.int_sort());
		    func_decl rho_primed_56 = function("rho_primed_56", c.real_sort(), c.real_sort());
		    
		    func_decl rho_65 = function("rho_65", c.int_sort(), c.int_sort());
		    func_decl rho_primed_65 = function("rho_primed_65", c.real_sort(), c.real_sort());
		    
		    expr pwl_56 = c.int_const("pwl_56");
		    s.add(pwl_56 >= (int)segLower + 1 && pwl_56 <= (int)segUpper);
		    
		    expr pwl_65 = c.int_const("pwl_65");
		    s.add(pwl_65 >= (int)segLower + 1 && pwl_65 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_56(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_56(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_65(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_65(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_56, t_after_56, implies(((t_before_56 < t_after_56) && (t_before_56 >= (int)segLower + 1) && (t_before_56 <= (int)segUpper) && (t_after_56 >= (int)segLower) && (t_after_56 <= (int)segUpper)), ((rho_56(t_before_56) < rho_56(t_after_56)) && (rho_65(t_before_56) < rho_65(t_after_56))))));
			
			//mutual separation constraint
			s.add(forall(pred_5, pred_6, implies(((rho_56(pred_5) == pred_6) && (pred_5 >= (int)segLower + 1) && (pred_5 <= (int)segUpper) && (pred_6 >= (int)segLower) && (pred_6 <= (int)segUpper)), (c.real_val(delta) <= (((a_6_x(pred_6) - a_5_x(pred_5)) * (a_6_x(pred_6) - a_5_x(pred_5))) + ((a_6_y(pred_6) - a_5_y(pred_5)) * (a_6_y(pred_6) - a_5_y(pred_5))) + ((a_6_z(pred_6) - a_5_z(pred_5)) * (a_6_z(pred_6) - a_5_z(pred_5))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_56, implies(((pwl_56 >= (int)segLower + 1) && (pwl_56 <= (int)segUpper)), (rho_primed_56(pwl_56) == rho_56(c.int_val(pwl_56)) + ((pwl_56 - c.int_val(pwl_56)) * (rho_56(c.int_val(pwl_56) + 1) - rho_56(c.int_val(pwl_56))))))));
			s.add(forall(pwl_65, implies(((pwl_65 >= (int)segLower + 1) && (pwl_65 <= (int)segUpper)), (rho_primed_65(pwl_65) == rho_65(c.int_val(pwl_65)) + ((pwl_65 - c.int_val(pwl_65)) * (rho_65(c.int_val(pwl_65) + 1) - rho_65(c.int_val(pwl_65))))))));
			
			//inverse re-timing
			s.add(forall(t_56, implies(((t_56 >= (int)segLower) && (t_56 <= (int)segUpper)), (rho_65(rho_56(t_56)) == t_56))));

			// ================ AGENT 5 AND AGENT 6 END ================ //
			
			// =============== AGENT 5 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_57 = c.int_const("t_57");
		    s.add(t_57 >= (int)segLower + 1 && t_57 <= (int)segUpper);
		    
		    expr t_before_57 = c.int_const("t_before_57");
		    expr t_after_57 = c.int_const("t_after_57");
		    s.add(t_before_57 >= (int)segLower + 1 && t_before_57 <= (int)segUpper && t_after_57 >= (int)segLower && t_after_57 <= (int)segUpper);
		    
		    func_decl rho_57 = function("rho_57", c.int_sort(), c.int_sort());
		    func_decl rho_primed_57 = function("rho_primed_57", c.real_sort(), c.real_sort());
		    
		    func_decl rho_75 = function("rho_75", c.int_sort(), c.int_sort());
		    func_decl rho_primed_75 = function("rho_primed_75", c.real_sort(), c.real_sort());
		    
		    expr pwl_57 = c.int_const("pwl_57");
		    s.add(pwl_57 >= (int)segLower + 1 && pwl_57 <= (int)segUpper);
		    
		    expr pwl_75 = c.int_const("pwl_75");
		    s.add(pwl_75 >= (int)segLower + 1 && pwl_75 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_57(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_57(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_75(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_75(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_57, t_after_57, implies(((t_before_57 < t_after_57) && (t_before_57 >= (int)segLower + 1) && (t_before_57 <= (int)segUpper) && (t_after_57 >= (int)segLower) && (t_after_57 <= (int)segUpper)), ((rho_57(t_before_57) < rho_57(t_after_57)) && (rho_75(t_before_57) < rho_75(t_after_57))))));
			
			//mutual separation constraint
			s.add(forall(pred_5, pred_7, implies(((rho_57(pred_5) == pred_7) && (pred_5 >= (int)segLower + 1) && (pred_5 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_5_x(pred_5)) * (a_7_x(pred_7) - a_5_x(pred_5))) + ((a_7_y(pred_7) - a_5_y(pred_5)) * (a_7_y(pred_7) - a_5_y(pred_5))) + ((a_7_z(pred_7) - a_5_z(pred_5)) * (a_7_z(pred_7) - a_5_z(pred_5))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_57, implies(((pwl_57 >= (int)segLower + 1) && (pwl_57 <= (int)segUpper)), (rho_primed_57(pwl_57) == rho_57(c.int_val(pwl_57)) + ((pwl_57 - c.int_val(pwl_57)) * (rho_57(c.int_val(pwl_57) + 1) - rho_57(c.int_val(pwl_57))))))));
			s.add(forall(pwl_75, implies(((pwl_75 >= (int)segLower + 1) && (pwl_75 <= (int)segUpper)), (rho_primed_75(pwl_75) == rho_75(c.int_val(pwl_75)) + ((pwl_75 - c.int_val(pwl_75)) * (rho_75(c.int_val(pwl_75) + 1) - rho_75(c.int_val(pwl_75))))))));
			
			//inverse re-timing
			s.add(forall(t_57, implies(((t_57 >= (int)segLower) && (t_57 <= (int)segUpper)), (rho_75(rho_57(t_57)) == t_57))));

			// ================ AGENT 5 AND AGENT 7 END ================ //
			
			// =============== AGENT 5 AND AGENT 8 START =============== //
			
			//agent pair smt variables
			expr t_58 = c.int_const("t_58");
		    s.add(t_58 >= (int)segLower + 1 && t_58 <= (int)segUpper);
		    
		    expr t_before_58 = c.int_const("t_before_58");
		    expr t_after_58 = c.int_const("t_after_58");
		    s.add(t_before_58 >= (int)segLower + 1 && t_before_58 <= (int)segUpper && t_after_58 >= (int)segLower && t_after_58 <= (int)segUpper);
		    
		    func_decl rho_58 = function("rho_58", c.int_sort(), c.int_sort());
		    func_decl rho_primed_58 = function("rho_primed_58", c.real_sort(), c.real_sort());
		    
		    func_decl rho_85 = function("rho_85", c.int_sort(), c.int_sort());
		    func_decl rho_primed_85 = function("rho_primed_85", c.real_sort(), c.real_sort());
		    
		    expr pwl_58 = c.int_const("pwl_58");
		    s.add(pwl_58 >= (int)segLower + 1 && pwl_58 <= (int)segUpper);
		    
		    expr pwl_85 = c.int_const("pwl_85");
		    s.add(pwl_85 >= (int)segLower + 1 && pwl_85 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_58(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_58(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_85(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_85(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_58, t_after_58, implies(((t_before_58 < t_after_58) && (t_before_58 >= (int)segLower + 1) && (t_before_58 <= (int)segUpper) && (t_after_58 >= (int)segLower) && (t_after_58 <= (int)segUpper)), ((rho_58(t_before_58) < rho_58(t_after_58)) && (rho_85(t_before_58) < rho_85(t_after_58))))));
			
			//mutual separation constraint
			s.add(forall(pred_5, pred_8, implies(((rho_58(pred_5) == pred_8) && (pred_5 >= (int)segLower + 1) && (pred_5 <= (int)segUpper) && (pred_8 >= (int)segLower) && (pred_8 <= (int)segUpper)), (c.real_val(delta) <= (((a_8_x(pred_8) - a_5_x(pred_5)) * (a_8_x(pred_8) - a_5_x(pred_5))) + ((a_8_y(pred_8) - a_5_y(pred_5)) * (a_8_y(pred_8) - a_5_y(pred_5))) + ((a_8_z(pred_8) - a_5_z(pred_5)) * (a_8_z(pred_8) - a_5_z(pred_5))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_58, implies(((pwl_58 >= (int)segLower + 1) && (pwl_58 <= (int)segUpper)), (rho_primed_58(pwl_58) == rho_58(c.int_val(pwl_58)) + ((pwl_58 - c.int_val(pwl_58)) * (rho_58(c.int_val(pwl_58) + 1) - rho_58(c.int_val(pwl_58))))))));
			s.add(forall(pwl_85, implies(((pwl_85 >= (int)segLower + 1) && (pwl_85 <= (int)segUpper)), (rho_primed_85(pwl_85) == rho_85(c.int_val(pwl_85)) + ((pwl_85 - c.int_val(pwl_85)) * (rho_85(c.int_val(pwl_85) + 1) - rho_85(c.int_val(pwl_85))))))));
			
			//inverse re-timing
			s.add(forall(t_58, implies(((t_58 >= (int)segLower) && (t_58 <= (int)segUpper)), (rho_85(rho_58(t_58)) == t_58))));

			// ================ AGENT 5 AND AGENT 8 END ================ //
			
			// =============== AGENT 5 AND AGENT 9 START =============== //
			
			//agent pair smt variables
			expr t_59 = c.int_const("t_59");
		    s.add(t_59 >= (int)segLower + 1 && t_59 <= (int)segUpper);
		    
		    expr t_before_59 = c.int_const("t_before_59");
		    expr t_after_59 = c.int_const("t_after_59");
		    s.add(t_before_59 >= (int)segLower + 1 && t_before_59 <= (int)segUpper && t_after_59 >= (int)segLower && t_after_59 <= (int)segUpper);
		    
		    func_decl rho_59 = function("rho_59", c.int_sort(), c.int_sort());
		    func_decl rho_primed_59 = function("rho_primed_59", c.real_sort(), c.real_sort());
		    
		    func_decl rho_95 = function("rho_95", c.int_sort(), c.int_sort());
		    func_decl rho_primed_95 = function("rho_primed_95", c.real_sort(), c.real_sort());
		    
		    expr pwl_59 = c.int_const("pwl_59");
		    s.add(pwl_59 >= (int)segLower + 1 && pwl_59 <= (int)segUpper);
		    
		    expr pwl_95 = c.int_const("pwl_95");
		    s.add(pwl_95 >= (int)segLower + 1 && pwl_95 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_59(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_59(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_95(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_95(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_59, t_after_59, implies(((t_before_59 < t_after_59) && (t_before_59 >= (int)segLower + 1) && (t_before_59 <= (int)segUpper) && (t_after_59 >= (int)segLower) && (t_after_59 <= (int)segUpper)), ((rho_59(t_before_59) < rho_59(t_after_59)) && (rho_95(t_before_59) < rho_95(t_after_59))))));
			
			//mutual separation constraint
			s.add(forall(pred_5, pred_9, implies(((rho_59(pred_5) == pred_9) && (pred_5 >= (int)segLower + 1) && (pred_5 <= (int)segUpper) && (pred_9 >= (int)segLower) && (pred_9 <= (int)segUpper)), (c.real_val(delta) <= (((a_9_x(pred_9) - a_5_x(pred_5)) * (a_9_x(pred_9) - a_5_x(pred_5))) + ((a_9_y(pred_9) - a_5_y(pred_5)) * (a_9_y(pred_9) - a_5_y(pred_5))) + ((a_9_z(pred_9) - a_5_z(pred_5)) * (a_9_z(pred_9) - a_5_z(pred_5))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_59, implies(((pwl_59 >= (int)segLower + 1) && (pwl_59 <= (int)segUpper)), (rho_primed_59(pwl_59) == rho_59(c.int_val(pwl_59)) + ((pwl_59 - c.int_val(pwl_59)) * (rho_59(c.int_val(pwl_59) + 1) - rho_59(c.int_val(pwl_59))))))));
			s.add(forall(pwl_95, implies(((pwl_95 >= (int)segLower + 1) && (pwl_95 <= (int)segUpper)), (rho_primed_95(pwl_95) == rho_95(c.int_val(pwl_95)) + ((pwl_95 - c.int_val(pwl_95)) * (rho_95(c.int_val(pwl_95) + 1) - rho_95(c.int_val(pwl_95))))))));
			
			//inverse re-timing
			s.add(forall(t_59, implies(((t_59 >= (int)segLower) && (t_59 <= (int)segUpper)), (rho_95(rho_59(t_59)) == t_59))));

			// ================ AGENT 5 AND AGENT 9 END ================ //
			
			// =============== AGENT 6 AND AGENT 7 START =============== //
			
			//agent pair smt variables
			expr t_67 = c.int_const("t_67");
		    s.add(t_67 >= (int)segLower + 1 && t_67 <= (int)segUpper);
		    
		    expr t_before_67 = c.int_const("t_before_67");
		    expr t_after_67 = c.int_const("t_after_67");
		    s.add(t_before_67 >= (int)segLower + 1 && t_before_67 <= (int)segUpper && t_after_67 >= (int)segLower && t_after_67 <= (int)segUpper);
		    
		    func_decl rho_67 = function("rho_67", c.int_sort(), c.int_sort());
		    func_decl rho_primed_67 = function("rho_primed_67", c.real_sort(), c.real_sort());
		    
		    func_decl rho_76 = function("rho_76", c.int_sort(), c.int_sort());
		    func_decl rho_primed_76 = function("rho_primed_76", c.real_sort(), c.real_sort());
		    
		    expr pwl_67 = c.int_const("pwl_67");
		    s.add(pwl_67 >= (int)segLower + 1 && pwl_67 <= (int)segUpper);
		    
		    expr pwl_76 = c.int_const("pwl_76");
		    s.add(pwl_76 >= (int)segLower + 1 && pwl_76 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_67(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_67(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_76(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_76(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_67, t_after_67, implies(((t_before_67 < t_after_67) && (t_before_67 >= (int)segLower + 1) && (t_before_67 <= (int)segUpper) && (t_after_67 >= (int)segLower) && (t_after_67 <= (int)segUpper)), ((rho_67(t_before_67) < rho_67(t_after_67)) && (rho_76(t_before_67) < rho_76(t_after_67))))));
			
			//mutual separation constraint
			s.add(forall(pred_6, pred_7, implies(((rho_67(pred_6) == pred_7) && (pred_6 >= (int)segLower + 1) && (pred_6 <= (int)segUpper) && (pred_7 >= (int)segLower) && (pred_7 <= (int)segUpper)), (c.real_val(delta) <= (((a_7_x(pred_7) - a_6_x(pred_6)) * (a_7_x(pred_7) - a_6_x(pred_6))) + ((a_7_y(pred_7) - a_6_y(pred_6)) * (a_7_y(pred_7) - a_6_y(pred_6))) + ((a_7_z(pred_7) - a_6_z(pred_6)) * (a_7_z(pred_7) - a_6_z(pred_6))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_67, implies(((pwl_67 >= (int)segLower + 1) && (pwl_67 <= (int)segUpper)), (rho_primed_67(pwl_67) == rho_67(c.int_val(pwl_67)) + ((pwl_67 - c.int_val(pwl_67)) * (rho_67(c.int_val(pwl_67) + 1) - rho_67(c.int_val(pwl_67))))))));
			s.add(forall(pwl_76, implies(((pwl_76 >= (int)segLower + 1) && (pwl_76 <= (int)segUpper)), (rho_primed_76(pwl_76) == rho_76(c.int_val(pwl_76)) + ((pwl_76 - c.int_val(pwl_76)) * (rho_76(c.int_val(pwl_76) + 1) - rho_76(c.int_val(pwl_76))))))));
			
			//inverse re-timing
			s.add(forall(t_67, implies(((t_67 >= (int)segLower) && (t_67 <= (int)segUpper)), (rho_76(rho_67(t_67)) == t_67))));

			// ================ AGENT 6 AND AGENT 7 END ================ //
			
			// =============== AGENT 6 AND AGENT 8 START =============== //
			
			//agent pair smt variables
			expr t_68 = c.int_const("t_68");
		    s.add(t_68 >= (int)segLower + 1 && t_68 <= (int)segUpper);
		    
		    expr t_before_68 = c.int_const("t_before_68");
		    expr t_after_68 = c.int_const("t_after_68");
		    s.add(t_before_68 >= (int)segLower + 1 && t_before_68 <= (int)segUpper && t_after_68 >= (int)segLower && t_after_68 <= (int)segUpper);
		    
		    func_decl rho_68 = function("rho_68", c.int_sort(), c.int_sort());
		    func_decl rho_primed_68 = function("rho_primed_68", c.real_sort(), c.real_sort());
		    
		    func_decl rho_86 = function("rho_86", c.int_sort(), c.int_sort());
		    func_decl rho_primed_86 = function("rho_primed_86", c.real_sort(), c.real_sort());
		    
		    expr pwl_68 = c.int_const("pwl_68");
		    s.add(pwl_68 >= (int)segLower + 1 && pwl_68 <= (int)segUpper);
		    
		    expr pwl_86 = c.int_const("pwl_86");
		    s.add(pwl_86 >= (int)segLower + 1 && pwl_86 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_68(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_68(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_86(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_86(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_68, t_after_68, implies(((t_before_68 < t_after_68) && (t_before_68 >= (int)segLower + 1) && (t_before_68 <= (int)segUpper) && (t_after_68 >= (int)segLower) && (t_after_68 <= (int)segUpper)), ((rho_68(t_before_68) < rho_68(t_after_68)) && (rho_86(t_before_68) < rho_86(t_after_68))))));
			
			//mutual separation constraint
			s.add(forall(pred_6, pred_8, implies(((rho_68(pred_6) == pred_8) && (pred_6 >= (int)segLower + 1) && (pred_6 <= (int)segUpper) && (pred_8 >= (int)segLower) && (pred_8 <= (int)segUpper)), (c.real_val(delta) <= (((a_8_x(pred_8) - a_6_x(pred_6)) * (a_8_x(pred_8) - a_6_x(pred_6))) + ((a_8_y(pred_8) - a_6_y(pred_6)) * (a_8_y(pred_8) - a_6_y(pred_6))) + ((a_8_z(pred_8) - a_6_z(pred_6)) * (a_8_z(pred_8) - a_6_z(pred_6))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_68, implies(((pwl_68 >= (int)segLower + 1) && (pwl_68 <= (int)segUpper)), (rho_primed_68(pwl_68) == rho_68(c.int_val(pwl_68)) + ((pwl_68 - c.int_val(pwl_68)) * (rho_68(c.int_val(pwl_68) + 1) - rho_68(c.int_val(pwl_68))))))));
			s.add(forall(pwl_86, implies(((pwl_86 >= (int)segLower + 1) && (pwl_86 <= (int)segUpper)), (rho_primed_86(pwl_86) == rho_86(c.int_val(pwl_86)) + ((pwl_86 - c.int_val(pwl_86)) * (rho_86(c.int_val(pwl_86) + 1) - rho_86(c.int_val(pwl_86))))))));
			
			//inverse re-timing
			s.add(forall(t_68, implies(((t_68 >= (int)segLower) && (t_68 <= (int)segUpper)), (rho_86(rho_68(t_68)) == t_68))));

			// ================ AGENT 6 AND AGENT 8 END ================ //
			
			// =============== AGENT 6 AND AGENT 9 START =============== //
			
			//agent pair smt variables
			expr t_69 = c.int_const("t_69");
		    s.add(t_69 >= (int)segLower + 1 && t_69 <= (int)segUpper);
		    
		    expr t_before_69 = c.int_const("t_before_69");
		    expr t_after_69 = c.int_const("t_after_69");
		    s.add(t_before_69 >= (int)segLower + 1 && t_before_69 <= (int)segUpper && t_after_69 >= (int)segLower && t_after_69 <= (int)segUpper);
		    
		    func_decl rho_69 = function("rho_69", c.int_sort(), c.int_sort());
		    func_decl rho_primed_69 = function("rho_primed_69", c.real_sort(), c.real_sort());
		    
		    func_decl rho_96 = function("rho_96", c.int_sort(), c.int_sort());
		    func_decl rho_primed_96 = function("rho_primed_96", c.real_sort(), c.real_sort());
		    
		    expr pwl_69 = c.int_const("pwl_69");
		    s.add(pwl_69 >= (int)segLower + 1 && pwl_69 <= (int)segUpper);
		    
		    expr pwl_96 = c.int_const("pwl_96");
		    s.add(pwl_96 >= (int)segLower + 1 && pwl_96 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_69(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_69(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_96(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_96(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_69, t_after_69, implies(((t_before_69 < t_after_69) && (t_before_69 >= (int)segLower + 1) && (t_before_69 <= (int)segUpper) && (t_after_69 >= (int)segLower) && (t_after_69 <= (int)segUpper)), ((rho_69(t_before_69) < rho_69(t_after_69)) && (rho_96(t_before_69) < rho_96(t_after_69))))));
			
			//mutual separation constraint
			s.add(forall(pred_6, pred_9, implies(((rho_69(pred_6) == pred_9) && (pred_6 >= (int)segLower + 1) && (pred_6 <= (int)segUpper) && (pred_9 >= (int)segLower) && (pred_9 <= (int)segUpper)), (c.real_val(delta) <= (((a_9_x(pred_9) - a_6_x(pred_6)) * (a_9_x(pred_9) - a_6_x(pred_6))) + ((a_9_y(pred_9) - a_6_y(pred_6)) * (a_9_y(pred_9) - a_6_y(pred_6))) + ((a_9_z(pred_9) - a_6_z(pred_6)) * (a_9_z(pred_9) - a_6_z(pred_6))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_69, implies(((pwl_69 >= (int)segLower + 1) && (pwl_69 <= (int)segUpper)), (rho_primed_69(pwl_69) == rho_69(c.int_val(pwl_69)) + ((pwl_69 - c.int_val(pwl_69)) * (rho_69(c.int_val(pwl_69) + 1) - rho_69(c.int_val(pwl_69))))))));
			s.add(forall(pwl_96, implies(((pwl_96 >= (int)segLower + 1) && (pwl_96 <= (int)segUpper)), (rho_primed_96(pwl_96) == rho_96(c.int_val(pwl_96)) + ((pwl_96 - c.int_val(pwl_96)) * (rho_96(c.int_val(pwl_96) + 1) - rho_96(c.int_val(pwl_96))))))));
			
			//inverse re-timing
			s.add(forall(t_69, implies(((t_69 >= (int)segLower) && (t_69 <= (int)segUpper)), (rho_96(rho_69(t_69)) == t_69))));

			// ================ AGENT 6 AND AGENT 9 END ================ //
			
			// =============== AGENT 7 AND AGENT 8 START =============== //
			
			//agent pair smt variables
			expr t_78 = c.int_const("t_78");
		    s.add(t_78 >= (int)segLower + 1 && t_78 <= (int)segUpper);
		    
		    expr t_before_78 = c.int_const("t_before_78");
		    expr t_after_78 = c.int_const("t_after_78");
		    s.add(t_before_78 >= (int)segLower + 1 && t_before_78 <= (int)segUpper && t_after_78 >= (int)segLower && t_after_78 <= (int)segUpper);
		    
		    func_decl rho_78 = function("rho_78", c.int_sort(), c.int_sort());
		    func_decl rho_primed_78 = function("rho_primed_78", c.real_sort(), c.real_sort());
		    
		    func_decl rho_87 = function("rho_87", c.int_sort(), c.int_sort());
		    func_decl rho_primed_87 = function("rho_primed_87", c.real_sort(), c.real_sort());
		    
		    expr pwl_78 = c.int_const("pwl_78");
		    s.add(pwl_78 >= (int)segLower + 1 && pwl_78 <= (int)segUpper);
		    
		    expr pwl_87 = c.int_const("pwl_87");
		    s.add(pwl_87 >= (int)segLower + 1 && pwl_87 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_78(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_78(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_87(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_87(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_78, t_after_78, implies(((t_before_78 < t_after_78) && (t_before_78 >= (int)segLower + 1) && (t_before_78 <= (int)segUpper) && (t_after_78 >= (int)segLower) && (t_after_78 <= (int)segUpper)), ((rho_78(t_before_78) < rho_78(t_after_78)) && (rho_87(t_before_78) < rho_87(t_after_78))))));
			
			//mutual separation constraint
			s.add(forall(pred_7, pred_8, implies(((rho_78(pred_7) == pred_8) && (pred_7 >= (int)segLower + 1) && (pred_7 <= (int)segUpper) && (pred_8 >= (int)segLower) && (pred_8 <= (int)segUpper)), (c.real_val(delta) <= (((a_8_x(pred_8) - a_7_x(pred_7)) * (a_8_x(pred_8) - a_7_x(pred_7))) + ((a_8_y(pred_8) - a_7_y(pred_7)) * (a_8_y(pred_8) - a_7_y(pred_7))) + ((a_8_z(pred_8) - a_7_z(pred_7)) * (a_8_z(pred_8) - a_7_z(pred_7))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_78, implies(((pwl_78 >= (int)segLower + 1) && (pwl_78 <= (int)segUpper)), (rho_primed_78(pwl_78) == rho_78(c.int_val(pwl_78)) + ((pwl_78 - c.int_val(pwl_78)) * (rho_78(c.int_val(pwl_78) + 1) - rho_78(c.int_val(pwl_78))))))));
			s.add(forall(pwl_87, implies(((pwl_87 >= (int)segLower + 1) && (pwl_87 <= (int)segUpper)), (rho_primed_87(pwl_87) == rho_87(c.int_val(pwl_87)) + ((pwl_87 - c.int_val(pwl_87)) * (rho_87(c.int_val(pwl_87) + 1) - rho_87(c.int_val(pwl_87))))))));
			
			//inverse re-timing
			s.add(forall(t_78, implies(((t_78 >= (int)segLower) && (t_78 <= (int)segUpper)), (rho_87(rho_78(t_78)) == t_78))));

			// ================ AGENT 7 AND AGENT 8 END ================ //
			
			// =============== AGENT 7 AND AGENT 9 START =============== //
			
			//agent pair smt variables
			expr t_79 = c.int_const("t_79");
		    s.add(t_79 >= (int)segLower + 1 && t_79 <= (int)segUpper);
		    
		    expr t_before_79 = c.int_const("t_before_79");
		    expr t_after_79 = c.int_const("t_after_79");
		    s.add(t_before_79 >= (int)segLower + 1 && t_before_79 <= (int)segUpper && t_after_79 >= (int)segLower && t_after_79 <= (int)segUpper);
		    
		    func_decl rho_79 = function("rho_79", c.int_sort(), c.int_sort());
		    func_decl rho_primed_79 = function("rho_primed_79", c.real_sort(), c.real_sort());
		    
		    func_decl rho_97 = function("rho_97", c.int_sort(), c.int_sort());
		    func_decl rho_primed_97 = function("rho_primed_97", c.real_sort(), c.real_sort());
		    
		    expr pwl_79 = c.int_const("pwl_79");
		    s.add(pwl_79 >= (int)segLower + 1 && pwl_79 <= (int)segUpper);
		    
		    expr pwl_97 = c.int_const("pwl_97");
		    s.add(pwl_97 >= (int)segLower + 1 && pwl_97 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_79(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_79(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_97(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_97(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_79, t_after_79, implies(((t_before_79 < t_after_79) && (t_before_79 >= (int)segLower + 1) && (t_before_79 <= (int)segUpper) && (t_after_79 >= (int)segLower) && (t_after_79 <= (int)segUpper)), ((rho_79(t_before_79) < rho_79(t_after_79)) && (rho_97(t_before_79) < rho_97(t_after_79))))));
			
			//mutual separation constraint
			s.add(forall(pred_7, pred_9, implies(((rho_79(pred_7) == pred_9) && (pred_7 >= (int)segLower + 1) && (pred_7 <= (int)segUpper) && (pred_9 >= (int)segLower) && (pred_9 <= (int)segUpper)), (c.real_val(delta) <= (((a_9_x(pred_9) - a_7_x(pred_7)) * (a_9_x(pred_9) - a_7_x(pred_7))) + ((a_9_y(pred_9) - a_7_y(pred_7)) * (a_9_y(pred_9) - a_7_y(pred_7))) + ((a_9_z(pred_9) - a_7_z(pred_7)) * (a_9_z(pred_9) - a_7_z(pred_7))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_79, implies(((pwl_79 >= (int)segLower + 1) && (pwl_79 <= (int)segUpper)), (rho_primed_79(pwl_79) == rho_79(c.int_val(pwl_79)) + ((pwl_79 - c.int_val(pwl_79)) * (rho_79(c.int_val(pwl_79) + 1) - rho_79(c.int_val(pwl_79))))))));
			s.add(forall(pwl_97, implies(((pwl_97 >= (int)segLower + 1) && (pwl_97 <= (int)segUpper)), (rho_primed_97(pwl_97) == rho_97(c.int_val(pwl_97)) + ((pwl_97 - c.int_val(pwl_97)) * (rho_97(c.int_val(pwl_97) + 1) - rho_97(c.int_val(pwl_97))))))));
			
			//inverse re-timing
			s.add(forall(t_79, implies(((t_79 >= (int)segLower) && (t_79 <= (int)segUpper)), (rho_97(rho_79(t_79)) == t_79))));

			// ================ AGENT 7 AND AGENT 9 END ================ //
			
			// =============== AGENT 8 AND AGENT 9 START =============== //
			
			//agent pair smt variables
			expr t_89 = c.int_const("t_89");
		    s.add(t_89 >= (int)segLower + 1 && t_89 <= (int)segUpper);
		    
		    expr t_before_89 = c.int_const("t_before_89");
		    expr t_after_89 = c.int_const("t_after_89");
		    s.add(t_before_89 >= (int)segLower + 1 && t_before_89 <= (int)segUpper && t_after_89 >= (int)segLower && t_after_89 <= (int)segUpper);
		    
		    func_decl rho_89 = function("rho_89", c.int_sort(), c.int_sort());
		    func_decl rho_primed_89 = function("rho_primed_89", c.real_sort(), c.real_sort());
		    
		    func_decl rho_98 = function("rho_98", c.int_sort(), c.int_sort());
		    func_decl rho_primed_98 = function("rho_primed_98", c.real_sort(), c.real_sort());
		    
		    expr pwl_89 = c.int_const("pwl_89");
		    s.add(pwl_89 >= (int)segLower + 1 && pwl_89 <= (int)segUpper);
		    
		    expr pwl_98 = c.int_const("pwl_98");
		    s.add(pwl_98 >= (int)segLower + 1 && pwl_98 <= (int)segUpper);
		    
		    //smt constraints
		    //range within epsilon constraint
		    for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_89(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_89(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			for(int j = segLower + 1; j <= segUpper; j++)
			{
				expr_vector eps_range(c);
				
				if(j == 0)	//special case when retiming from t0
				{
					for(int k = j; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_98(j) == k);
					}
				}
				else		//all other re-timings
				{
					for(int k = j - 1; k <= j + 1 ; k++)
					{
						eps_range.push_back(rho_98(j) == k);
					}
				}
				
				s.add(mk_or(eps_range));
			}
			
			//order preservation constraint
			s.add(forall(t_before_89, t_after_89, implies(((t_before_89 < t_after_89) && (t_before_89 >= (int)segLower + 1) && (t_before_89 <= (int)segUpper) && (t_after_89 >= (int)segLower) && (t_after_89 <= (int)segUpper)), ((rho_89(t_before_89) < rho_89(t_after_89)) && (rho_98(t_before_89) < rho_98(t_after_89))))));
			
			//mutual separation constraint
			s.add(forall(pred_8, pred_9, implies(((rho_89(pred_8) == pred_9) && (pred_8 >= (int)segLower + 1) && (pred_8 <= (int)segUpper) && (pred_9 >= (int)segLower) && (pred_9 <= (int)segUpper)), (c.real_val(delta) <= (((a_9_x(pred_9) - a_8_x(pred_8)) * (a_9_x(pred_9) - a_8_x(pred_8))) + ((a_9_y(pred_9) - a_8_y(pred_8)) * (a_9_y(pred_9) - a_8_y(pred_8))) + ((a_9_z(pred_9) - a_8_z(pred_8)) * (a_9_z(pred_9) - a_8_z(pred_8))))))));
			
			//piece-wise linear interpolation
			s.add(forall(pwl_89, implies(((pwl_89 >= (int)segLower + 1) && (pwl_89 <= (int)segUpper)), (rho_primed_89(pwl_89) == rho_89(c.int_val(pwl_89)) + ((pwl_89 - c.int_val(pwl_89)) * (rho_89(c.int_val(pwl_89) + 1) - rho_89(c.int_val(pwl_89))))))));
			s.add(forall(pwl_98, implies(((pwl_98 >= (int)segLower + 1) && (pwl_98 <= (int)segUpper)), (rho_primed_98(pwl_98) == rho_98(c.int_val(pwl_98)) + ((pwl_98 - c.int_val(pwl_98)) * (rho_98(c.int_val(pwl_98) + 1) - rho_98(c.int_val(pwl_98))))))));
			
			//inverse re-timing
			s.add(forall(t_89, implies(((t_89 >= (int)segLower) && (t_89 <= (int)segUpper)), (rho_98(rho_89(t_89)) == t_89))));

			// ================ AGENT 8 AND AGENT 9 END ================ //
			
			if(s.check() == sat)
		    {
		    	std::string verdict = std::to_string(i) + " : Sat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    else
		    {
		    	std::string verdict = std::to_string(i) + " : Unsat";
		    	//std::cout << verdict << std::endl;
		    	verdicts.push_back(verdict);
			}
		    
		    //reset solver
		    //s.reset();
		    
		    //build and show model
		    //model m = s.get_model();
    		//std::cout << m << "\n";
	    }
	}
	//return verdicts;
}

int main() {
	//runtime measuring variables
	struct timeval start, finish;
	
	int agentCount;
	std::cout << "Number of agents : " << std::endl;
	std::cin >> agentCount;
	
	double eps;
	std::cout << "Epsilon : " << std::endl;
	std::cin >> eps;
	
	double sigStart;
	std::cout << "Signal start : " << std::endl;
	std::cin >> sigStart;
	
	double sigEnd;
	std::cout << "Signal end : " << std::endl;
	std::cin >> sigEnd;
	
	int segStart;
	std::cout << "Segment start : " << std::endl;
	std::cin >> segStart;
	
	int segEnd;
	std::cout << "Segment end : " << std::endl;
	std::cin >> segEnd;
	
	int repeat;
	std::cout << "Repeat : " << std::endl;
	std::cin >> repeat;
	
	for(int i = sigEnd; i <= sigStart; i--)
	{
		for(int j = segEnd; j <= segStart; j--)
		{
			std::cout << "Signal Length : " << i << std::endl;
			std::cout << "Segments : " << j << std::endl;
			
			double total_t = 0;
			
			for(int k = 0; k < repeat; k++)
			{
				gettimeofday(&start, NULL);
				
				if(agentCount == 2)
				{
					runSolver_2(eps, j, i, 0);
				}
				if(agentCount == 3)
				{
					runSolver_3(eps, j, i, 0);
				}
				if(agentCount == 4)
				{
					runSolver_4(eps, j, i, 0);
				}
				if(agentCount == 5)
				{
					runSolver_5(eps, j, i, 0);
				}
				if(agentCount == 6)
				{
					runSolver_6(eps, j, i, 0);
				}
				if(agentCount == 7)
				{
					runSolver_7(eps, j, i, 0);
				}
				if(agentCount == 8)
				{
					runSolver_8(eps, j, i, 0);
				}
				if(agentCount == 9)
				{
					runSolver_9(eps, j, i, 0);
				}
				
				gettimeofday(&finish, NULL);
				
				double rt = ((finish.tv_sec - start.tv_sec)*1000000L+finish.tv_usec) - start.tv_usec;
				std::cout << "Runtime : " << rt << std::endl;
				
				total_t += rt;
			}
			
			std::cout << "Average Runtime : " << total_t / repeat << std::endl;
		}
	}
	
    //getData test
    //printData(getData("agent_0.txt"));
    
    //evalSolver test
    //evalSolvers(getSolvers());
    //gettimeofday(&start, NULL);
    
    //runSolver_10(0.05, 4, 1, 0);
    //z3_test(5);
    
    //gettimeofday(&finish, NULL);
    //std::cout << ((finish.tv_sec - start.tv_sec)*1000000L+finish.tv_usec) - start.tv_usec << std::endl;
    
    //parallelExec Test
    //gettimeofday(&start, NULL);
    
    //parallelExec();
    
    //gettimeofday(&finish, NULL);
    //std::cout << ((finish.tv_sec - start.tv_sec)*1000000L+finish.tv_usec) - start.tv_usec << std::endl;
	
    return 0;
}
