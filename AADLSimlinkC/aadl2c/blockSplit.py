
import re
import numpy
import pandas
import codecs


global_thread_name = []
global_thread_out_port = []
global_process_name = []
global_process_out_port = []
global_system_name = []
global_system_out_port = []

def firstParserName(file_in):
    '''scan the global file and split the name of each component'''

    with codecs.open(file_in, 'r', encoding='utf-8') as in_f:
        f_sentence = []
        for line in in_f.readlines():
            line = line.split('\n')
            f_sentence.append(line[0])

        for sentence in f_sentence:
            # system name paser
            if re.search('SYSTEM', sentence) and not re.search(':', sentence) and not re.search('IMPLEMENTATION', sentence):
                system_name = sentence.strip().replace('SYSTEM','').replace(' ', '').replace('\n', '')
                global_system_name.append(system_name)


            # process name paser
            if re.search('PROCESS', sentence) and not re.search(':', sentence) and not re.search('PROCESSOR', sentence) and not re.search('IMPLEMENTATION', sentence):
                process_name = sentence.strip().replace('PROCESS','').replace(' ', '').replace('\n','')
                global_process_name.append(process_name)


            # thread name parser
            if re.search('THREAD', sentence) and not re.search(':', sentence) and not re.search('IMPLEMENTATION', sentence):
                thread_name = sentence.strip().replace('THREAD','').replace(' ', '').replace('\n', '')
                global_thread_name.append(thread_name)

    #print(global_system_name)
    #print(global_process_name)
    #print(global_thread_name)


def blockSplit(file_in):

    with codecs.open(file_in, 'r', encoding="utf-8") as in_f:
        f_sentence = []
        for line in in_f.readlines():
            line = line.split('\n')
            #print(line[0])
            f_sentence.append(line[0])
        #for l in f_sentence:
        #    print(l)
        global_sentence = []

        end_flag = 0
        for sentence in f_sentence:
            #if re.search('THREAD', sentence):
            #    thread_flag = 1
                #system_sentence.append(sentence)
            if re.search('END', sentence):
                end_flag +=1
            if end_flag <=2:
                if sentence.strip() !='' and not re.search('PACKAGE', sentence):
                    global_sentence.append(sentence)

                if end_flag == 1:
                    first_sentence = global_sentence[0]
                    if re.search('PROCESSOR', first_sentence):
                        processor_model(global_sentence)
                        global_sentence = []
                        end_flag = 0
                    if re.search('MEMORY', first_sentence):
                        #print(first_sentence)
                        global_sentence = []
                        end_flag = 0


                if end_flag ==2:
                    #thread_flag = 0
                    end_flag = 0
                    first_sentence = global_sentence[0]
                    if re.search('THREAD', first_sentence):
                        #print(first_sentence) ###transfer model interface
                        thread_model(global_sentence)
                        global_sentence = []
                    elif re.search('SYSTEM', first_sentence):
                        #print(first_sentence)
                        system_model(global_sentence)
                        global_sentence = []
                    elif re.search('PROCESS', first_sentence):
                        #print(first_sentence)
                        process_model(global_sentence)
                        global_sentence = []
                    else:
                        #print(first_sentence)
                        global_sentence = []


def system_model(system_sentences):
    in_port = []
    out_port = []
    # Property = []
    p_process_name = []
    cnx_in_rlt = []
    cnx_out_rlt = []
    s_process_port = []

    for sentence in system_sentences:
        # system name paser
        if re.search('SYSTEM', sentence) and not re.search('IMPLEMENTATION', sentence):
            system_name = sentence.strip().replace('SYSTEM','').replace(' ', '').replace('\n', '')
            #print(system_name)
            #global_system_name.append(system_name)

        # data port parser
        if (re.search('EVENT', sentence) or re.search('DATA', sentence)) and re.search('PORT', sentence):
            if re.search('IN', sentence):
                port_name = sentence.strip('\n').strip(' ').split(':')[0]
                port_name = 'system_' + system_name + '_' + port_name
                in_port.append(port_name)
            if re.search('OUT', sentence):
                port_name = sentence.strip('\n').strip(' ').split(':')[0]
                port_name = 'system_' + system_name + '_' + port_name
                out_port.append(port_name)
                global_system_out_port.append(port_name)

        # process parser
        if re.search('PROCESS', sentence) and not re.search('PROCESSOR', sentence):
            sentence = sentence.strip('\n').replace(' ', '')
            sentence = sentence.split(':')
            process_name = sentence[0]
            p_process_name.append(process_name)

        # port connection relationship parser
        if re.search(':', str(sentence)) and re.search('->', str(sentence)):
            sentence = sentence.strip('\n').replace(';','').replace(' ','').replace('PORT','')
            sentence = sentence.split(':')[1]
            sentence = sentence.split('->')
            cnx_in_port = sentence[0]
            # the symbol '\r' makes a big problem, remember to replace it
            cnx_out_port = sentence[1]

            #print(cnx_in_port)
            #print(cnx_out_port)
            if not re.search('\.', cnx_in_port) and re.search('\.', cnx_out_port):
                cnx_out_port = cnx_out_port.replace('.', '_').replace('\r', '')
                p_out_port = 'process_' + cnx_out_port
                s_process_port.append(p_out_port)
                cnx = 'int process_' + cnx_out_port + ' = ' + 'system_'+ system_name + '_' + cnx_in_port + ';'
                cnx_in_rlt.append(cnx)
                #print(cnx_in_rlt)
            if not re.search('\.', cnx_out_port) and re.search('\.', cnx_in_port):
                cnx_in_port = cnx_in_port.replace('.','_').replace('\r','')
                cnx_out_port = cnx_out_port.replace('\r','')
                cnx = '// system_' + system_name + '_' + cnx_out_port + ' = ' + 'process_' + cnx_in_port + ';'
                cnx_out_rlt.append(cnx)
                #print(cnx_out_rlt)


    if len(out_port) == 1:
        out_f = 'int system_' + system_name + '(' + 'int ' + ', int '.join(in_port) + ',' \
            + 'THREAD *thread_' + ', THREAD *thread_'.join(global_thread_name) + '){' + '\n' \
            + '\t' + '\n\t'.join(cnx_in_rlt) + '\n' \
            + '\t' + '\n\t'.join(cnx_out_rlt) + '\n' \
            + '\t' + 'return ' + out_port[0] + ';' + '\n' \
            + '};' + '\n'

    if len(out_port) > 1:
        #print(out_port[1])
        result_sent = []
        for idx, p_name in enumerate(out_port):
            result_f = 'result[' + str(idx) + '] = ' + '*(result_p + ' + str(idx) +  ');'
            result_sent.append(result_f)

        out_f = 'int system_' + system_name + '(' + 'int ' + ', int '.join(in_port) + ',' \
                + 'THREAD *thread_' + ', THREAD *thread_'.join(global_thread_name) + '){' + '\n' \
                + '\t' + '\n\t'.join(cnx_in_rlt) + '\n' \
                + '\t' + '\n\t'.join(cnx_out_rlt) + '\n' \
                + '\t' + 'static int result[' + str(len(out_port)) + ']' + ';' + '\n' \
                + '\t' + 'int *result_p;' + '\n' \
                + '\t' + 'result_p = ' + 'process_' + global_process_name[0] + '(' + ', '.join(s_process_port) +','\
                + 'thread_' + ', thread_'.join(global_thread_name) +');' + '\n'\
                + '\t' + '\n\t'.join(result_sent) + '\n' \
                + '\t' + 'return result' + ';' + '\n' \
                + '};' + '\n'

    with open('conditioner.c','a') as out_c_f:
        out_c_f.write(out_f + '\n')



def processor_model(processor_sentences):

    Property = []

    for sentence in processor_sentences:
        ##scheduling protocol parser
        if re.search('Scheduling_Protocol', sentence):
            sch_prtl = re.findall('\((.*?)\)', sentence)[0]
            Property.append(sch_prtl)
            #print(sch_prtl)


def process_model(process_sentences):
    in_port = []
    out_port = []
    #Property = []
    p_thread_name = []
    cnx_in_rlt = []
    cnx_out_rlt = []

    for sentence in process_sentences:
        ##process name parser
        if re.search('PROCESS', sentence) and not re.search('IMPLEMENTATION', sentence):
            process_name = sentence.strip().strip('PROCESS').replace(' ', '').replace('\n','')
            #global_process_name.append(process_name)

        ##data port parser
        if (re.search('EVENT',sentence) or re.search('DATA',sentence)) and re.search('PORT', sentence):
            if re.search('IN', sentence):
                port_name = sentence.strip('\n').strip(' ').split(':')[0]
                port_name = 'process_' + process_name + '_' + port_name
                in_port.append(port_name)
            if re.search('OUT', sentence):
                port_name = sentence.strip('\n').strip(' ').split(':')[0]
                port_name = 'process_' + process_name + '_' + port_name
                out_port.append(port_name)
                global_process_out_port.append(port_name)

        # thread name parser
        if re.search('THREAD', sentence):
            sentence = sentence.strip('\n').replace(' ', '')
            sentence = sentence.split(':')
            thread_name = sentence[0]
            p_thread_name.append(thread_name)

        # port connection relationship parser
        if re.search(':', str(sentence)) and re.search('->', str(sentence)):
            sentence = sentence.strip('\n').replace(';','').replace(' ','').replace('PORT','')
            sentence = sentence.split(':')[1]
            sentence = sentence.split('->')
            cnx_in_port = sentence[0]
            # the symbol '\r' makes a big problem, remember to replace it
            cnx_out_port = sentence[1]

            #print(cnx_in_port)
            #print(cnx_out_port)
            if not re.search('\.', cnx_in_port) and re.search('\.', cnx_out_port):
                cnx_out_port = cnx_out_port.replace('.', '_').replace('\r', '')
                cnx = 'int thread_' + cnx_out_port + ' = ' + 'process_'+ process_name + '_' + cnx_in_port + ';'
                cnx_in_rlt.append(cnx)
                #print(cnx_in_rlt)
            if not re.search('\.', cnx_out_port) and re.search('\.', cnx_in_port):
                cnx_in_port = cnx_in_port.replace('.','_').replace('\r','')
                cnx_out_port = cnx_out_port.replace('\r','')
                cnx = 'process_' + process_name + '_' + cnx_out_port + ' = ' + 'thread_' + cnx_in_port + ';'
                cnx_out_rlt.append(cnx)
                #print(cnx_out_rlt)


    # write in C file
    thread_sent = []
    for t_name in p_thread_name:
        result_f = 'insert(thread_' + t_name +')' + ';'
        thread_sent.append(result_f)

    if len(out_port) == 1:
        out_f = 'int process_' + process_name + '(' + 'int ' + ', int '.join(in_port) + ','\
            + 'THREAD *thread_' + ', THREAD *thread_'.join(p_thread_name) + '){' + '\n' \
            + '\t' + '\n\t'.join(cnx_in_rlt) + '\n' \
            + '\t' + '\n\t'.join(thread_sent) + '\n' \
            + '\t' + 'CPU_schedule_thread();' + '\n' \
            + '\t' + '\n\t'.join(cnx_out_rlt) + '\n' \
            + '\t' + 'return ' + out_port[0] + ';' + '\n' \
            + '};' + '\n'

    if len(out_port) > 1:
        #print(out_port[1])
        result_sent = []
        for idx, p_name in enumerate(out_port):
            result_f = 'result[' + str(idx) + '] = ' + p_name + ';'
            result_sent.append(result_f)

        out_f = 'int process_' + process_name + '(' + 'int ' + ', int '.join(in_port) + ','\
                + 'THREAD *thread_' + ', THREAD *thread_'.join(p_thread_name) + '){' + '\n' \
                + '\t' + '\n\t'.join(cnx_in_rlt) + '\n' \
                + '\t' + '\n\t'.join(thread_sent) + '\n' \
                + '\t' + 'CPU_schedule_thread();' + '\n' \
                + '\t' + '\n\t'.join(cnx_out_rlt) + '\n' \
                + '\t' + 'static int result[' + str(len(out_port)) + ']' + ';' + '\n' \
                + '\t' + '\n\t'.join(result_sent) + '\n' \
                + '\t' + 'return result' + ';' + '\n' \
                + '};' + '\n'

    with open('conditioner.c','a') as out_c_f:
        out_c_f.write(out_f + '\n')


def thread_model(thread_sentences):
    in_port = []
    out_port = []
    pure_port = []
    Property = []
    kuohao_sentence = []
    var = ''
    kuohao_flag = fankuohao_flag = 0
    for sentence in thread_sentences:
        ##thread name parser
        if re.search('THREAD', sentence) and not re.search('IMPLEMENTATION', sentence):
            thread_name = sentence.strip().strip('THREAD').replace(' ', '').replace('\n','')
            #global_thread_name.append(thread_name)

        ##data port parser
        if (re.search('EVENT',sentence) or re.search('DATA',sentence)) and re.search('PORT', sentence):
            if re.search('IN', sentence):
                port_name = sentence.strip('\n').strip(' ').replace(' ', '').split(':')[0]
                pure_port.append(port_name)
                port_name = 'thread_' + thread_name + '_' + port_name
                in_port.append(port_name)
            if re.search('OUT', sentence):
                port_name = sentence.strip('\n').strip(' ').replace(' ','').split(':')[0]
                pure_port.append(port_name)
                port_name = 'thread_' + thread_name + '_' + port_name
                out_port.append(port_name)
                #global_thread_out_port.append(port_name)

        ##Priority parser
        if re.search('Priority', sentence):
            prio = sentence.strip('\n').replace('Priority', '').replace('=>', '').replace(';', '').strip(' ')
            Property.append(prio)
        if re.search('Dispatch_Protocol', sentence):
            protocol = sentence.strip('\n').replace('Dispatch_Protocol','').replace('=>','').replace(';','').strip(' ')
            Property.append(protocol)
        if re.search('Period', sentence):
            period = sentence.strip('\n').replace('Period', '').replace('=>', '').replace(';', '').strip(' ')
            Property.append(period)
        if re.search('Deadline', sentence):
            deadline = sentence.strip('\n').replace('Deadline', '').replace('=>', '').replace(';', '').strip(' ')
            Property.append(deadline)

        ## variable parser
        if re.search('VARIABLES', sentence):
            var = sentence.strip('\n').strip(' ').replace('VARIABLES', '').split(':')[0]
            #print(var)
            if var.strip() == '':
                var = 'var'

        ##behavior annex parser
        if re.search('\{', sentence) and not re.search('\*\*', sentence):
            #print ('{ } find')
            kuohao_flag = 1

        if re.search('\}', sentence) and not re.search('\*\*', sentence):
            fankuohao_flag = 1

        if kuohao_flag == 1 and fankuohao_flag != 1: 
            #print(sentence)
            #print(pure_port)
            for port in pure_port:
                #print(port)
                if re.search(port, sentence):
                    p_t_name = 'thread_' + thread_name +'_' + port
                    sentence = sentence.replace(port, p_t_name)
                    print(sentence)
                #if re.search('if', sentence) and re.search('end', sentence):
                    #sentence = sentence.replace('end if','}')
                    #sentence = sentence.replace(')','){')
            kuohao_sentence.append(sentence.replace('{',' ').replace(':=', '=').replace('end if;','}//').replace(')','){'))

        if fankuohao_flag == 1:
            kuohao_flag = 0
            fankuohao_flag = 0
            for port in pure_port:
                #print(port)
                if re.search(port, sentence):
                    p_t_name = 'thread_' + thread_name +'_' + port
                    sentence = sentence.replace(port, p_t_name)
                    print(sentence)
                #if re.search('if', sentence) and re.search('end', sentence):
                    #sentence = sentence.replace('end if','}')
                    #sentence = sentence.replace(')','){')
            if re.search('if', sentence):
                kuohao_sentence.append(sentence.replace('{',' ').replace('}', ' ').replace(':=', '=').replace('end if;','}//').replace(')','){'))
            if not re.search('if', sentence):
                kuohao_sentence.append(sentence.replace('{',' ').replace('}', ' ').replace(':=', '=').replace('end if;','}//').replace(')','){'))
    #print('\n'.join(kuohao_sentence))
    #print('in port: ' + '\t'.join(pure_port))
    #print('-----------------------------------')
    #print('out port: ' + '\t'.join(out_pure_port))
    #print('**********************************')

    if len(out_port) == 1:
        out_f = 'int thread_'+ thread_name + '(' + 'int ' + ', int '.join(in_port) + '){' + '\n' \
            + '\t' + 'int ' + var + ';' +'\n' \
            + ' '.join(kuohao_sentence) + '\n' \
            + '\t' + 'return ' + out_port[0] + ';' + '\n' \
            + '};' + '\n'
    if len(out_port) > 1:
        #print(out_port[1])
        result_sent = []
        for idx, p_name in enumerate(out_port):
            result_f = 'result[' + str(idx) + '] = ' + p_name + ';'
            result_sent.append(result_f)
        out_f = 'int *thread_' + thread_name + '(' + 'int ' + ', int '.join(in_port) + '){' + '\n' \
                + '\t' + 'int ' + var + ';' + '\n' \
                + ' '.join(kuohao_sentence) + '\n' \
                + '\t' + 'static int result['+ str(len(out_port)) + ']' + ';' + '\n' \
                + '\t' + '\n\t'.join(result_sent) + '\n' \
                + '\t' + 'return result' + ';' + '\n' \
                + '};' + '\n'

    with open('conditioner.c','a') as out_c_f:
        out_c_f.write(out_f + '\n')





if __name__=='__main__':
    file_in = 'conditioner.aadl'
    firstParserName(file_in)
    blockSplit(file_in)