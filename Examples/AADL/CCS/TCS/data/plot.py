import matplotlib.pyplot as plt
from matplotlib.backends.backend_pdf import PdfPages

# times0 = list()
# datas0 = list()
# # f = open("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/veh_v")
# # f = open("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/obs_pos")
# f = open("HCSP_v")
# for line in f.readlines():
#     time, data = line.split(',')
#     times0.append(float(time.strip()))
#     datas0.append(float(data.strip()))
#     if times0[-1] >= 40:
#         break
# f.close()

times1 = list()
datas1 = list()
# f = open("HCSP_v_2bus_3ms_p1s_obs")
# f = open("HCSP_v")
f = open("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/obs_pos")
for line in f.readlines():
    time, data = line.split(',')
    times1.append(float(time.strip()))
    datas1.append(float(data.strip()))
    if times1[-1] >= 40:
        break
f.close()

times2 = list()
datas2 = list()
# f = open("HCSP_v_3bus_5ms_p1s_obs")
f = open("HCSP_s_1bus_3ms")
# f = open("/Users/BEAR/Projects/mars/Examples/AADL/CCS/C/C/data/veh_pos")
for line in f.readlines():
    time, data = line.split(',')
    times2.append(float(time.strip()))
    datas2.append(float(data.strip()))
    if times2[-1] >= 40:
        break
f.close()

# fig = plt.figure(figsize=(12, 5))
fig = plt.figure(figsize=(6.5, 5))
# plt.plot(times0, datas0, color='k', linestyle='-', label="HCSP (no bus)")
plt.plot(times1, datas1, color='k', linestyle='-', label="obstacle")
plt.plot(times2, datas2, color='k', linestyle='--', label="vehicle (1bus, 3ms)")
plt.legend()  # loc="lower left"
plt.grid(c='#a1a3a6', linestyle='--', linewidth=0.5)
plt.xlabel("time (s)")
# plt.ylabel("vehicle velocity (m/s)")
# plt.xlabel("time (s)")
plt.ylabel("position (m)")
plt.ylim([-3, 102])
plt.show()
pdf = PdfPages('no_color_1bus3ms_positions.pdf')
pdf.savefig(fig)
pdf.close()
